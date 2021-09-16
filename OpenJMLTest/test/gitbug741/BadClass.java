public class BadClass implements BadInterface {
    protected BadInterface bi;
    public BadClass(BadInterface bi) {
        this.bi = bi;
    }
}
