BEGIN { srand() }
{
    sub(/ struct {/,sprintf(" struct mystruct_%010d {",rand()*10000000000))
    sub(/ struct{/,sprintf(" struct mystruct_%010d{",rand()*10000000000))
    print
}
