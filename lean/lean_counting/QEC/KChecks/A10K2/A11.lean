import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A10

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows3650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3650 = true := by
  rw [show A10K2.u3650 = KTree.node A10K2.u3646 (nat_lit 59600106) (nat_lit 12104196780) (nat_lit 0) A10K2.u3649 from rfl, allE_node, arows3646, irow3650, arows3649]
  all_goals rfl

theorem atot3650 : totK PA10K2 A10K2.u3650 = [0, 0, 1436473895890, 7854511400924, 14953466368590, 11121170199608, 3180440286156, 436728024509, 25565504801, 0] := by
  rw [show A10K2.u3650 = KTree.node A10K2.u3646 (nat_lit 59600106) (nat_lit 12104196780) (nat_lit 0) A10K2.u3649 from rfl, totK_node, atot3646, atot3649]
  decide +kernel

theorem arows3657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3657 = true := by
  rw [show A10K2.u3657 = KTree.node A10K2.u3653 (nat_lit 59633046) (nat_lit 16090923929) (nat_lit 0) A10K2.u3656 from rfl, allE_node, arows3653, irow3657, arows3656]
  all_goals rfl

theorem atot3657 : totK PA10K2 A10K2.u3657 = [0, 0, 1306223671615, 6991790020868, 13663297094910, 11573743676625, 4049538631396, 487358070591, 11138589073, 0] := by
  rw [show A10K2.u3657 = KTree.node A10K2.u3653 (nat_lit 59633046) (nat_lit 16090923929) (nat_lit 0) A10K2.u3656 from rfl, totK_node, atot3653, atot3656]
  decide +kernel

theorem arows3665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3665 = true := by
  rw [show A10K2.u3665 = KTree.node A10K2.u3661 (nat_lit 59670798) (nat_lit 10488841319) (nat_lit 0) A10K2.u3664 from rfl, allE_node, arows3661, irow3665, arows3664]
  all_goals rfl

theorem atot3665 : totK PA10K2 A10K2.u3665 = [0, 0, 810058863673, 6348066905544, 15221375958386, 12396075579156, 2673085160052, 131570038320, 0, 0] := by
  rw [show A10K2.u3665 = KTree.node A10K2.u3661 (nat_lit 59670798) (nat_lit 10488841319) (nat_lit 0) A10K2.u3664 from rfl, totK_node, atot3661, atot3664]
  decide +kernel

theorem arows3672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3672 = true := by
  rw [show A10K2.u3672 = KTree.node A10K2.u3668 (nat_lit 59728375) (nat_lit 14886314268) (nat_lit 0) A10K2.u3671 from rfl, allE_node, arows3668, irow3672, arows3671]
  all_goals rfl

theorem atot3672 : totK PA10K2 A10K2.u3672 = [0, 573258531646, 3691548198080, 9658706940544, 13332806291906, 9475596195327, 2750020964214, 277054461093, 6239673734, 0] := by
  rw [show A10K2.u3672 = KTree.node A10K2.u3668 (nat_lit 59728375) (nat_lit 14886314268) (nat_lit 0) A10K2.u3671 from rfl, totK_node, atot3668, atot3671]
  decide +kernel

theorem arows3681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3681 = true := by
  rw [show A10K2.u3681 = KTree.node A10K2.u3677 (nat_lit 59791580) (nat_lit 11107961971) (nat_lit 0) A10K2.u3680 from rfl, allE_node, arows3677, irow3681, arows3680]
  all_goals rfl

theorem atot3681 : totK PA10K2 A10K2.u3681 = [0, 1234121467409, 7051024860783, 14139208989299, 11510314073478, 3698004570384, 513517621062, 30650496230, 0, 0] := by
  rw [show A10K2.u3681 = KTree.node A10K2.u3677 (nat_lit 59791580) (nat_lit 11107961971) (nat_lit 0) A10K2.u3680 from rfl, totK_node, atot3677, atot3680]
  decide +kernel

theorem arows3688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3688 = true := by
  rw [show A10K2.u3688 = KTree.node A10K2.u3684 (nat_lit 59845120) (nat_lit 13679738792) (nat_lit 0) A10K2.u3687 from rfl, allE_node, arows3684, irow3688, arows3687]
  all_goals rfl

theorem atot3688 : totK PA10K2 A10K2.u3688 = [0, 1597535614651, 7992899222563, 14365720724044, 11007907186337, 3127000210605, 290234426166, 5546304973, 0, 0] := by
  rw [show A10K2.u3688 = KTree.node A10K2.u3684 (nat_lit 59845120) (nat_lit 13679738792) (nat_lit 0) A10K2.u3687 from rfl, totK_node, atot3684, atot3687]
  decide +kernel

theorem arows3696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3696 = true := by
  rw [show A10K2.u3696 = KTree.node A10K2.u3692 (nat_lit 59878628) (nat_lit 12040520169) (nat_lit 0) A10K2.u3695 from rfl, allE_node, arows3692, irow3696, arows3695]
  all_goals rfl

theorem atot3696 : totK PA10K2 A10K2.u3696 = [0, 502723522018, 4418115446486, 12857413101601, 14472548043943, 5806482157167, 758708834466, 31082886609, 0, 0] := by
  rw [show A10K2.u3696 = KTree.node A10K2.u3692 (nat_lit 59878628) (nat_lit 12040520169) (nat_lit 0) A10K2.u3695 from rfl, totK_node, atot3692, atot3695]
  decide +kernel

theorem arows3703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3703 = true := by
  rw [show A10K2.u3703 = KTree.node A10K2.u3699 (nat_lit 59907469) (nat_lit 2893580867) (nat_lit 0) A10K2.u3702 from rfl, allE_node, arows3699, irow3703, arows3702]
  all_goals rfl

theorem atot3703 : totK PA10K2 A10K2.u3703 = [0, 1985486290667, 9176964676589, 14608122747146, 9530961018398, 2590639651548, 267463799553, 6121173289, 0, 0] := by
  rw [show A10K2.u3703 = KTree.node A10K2.u3699 (nat_lit 59907469) (nat_lit 2893580867) (nat_lit 0) A10K2.u3702 from rfl, totK_node, atot3699, atot3702]
  decide +kernel

theorem arows3714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3714 = true := by
  rw [show A10K2.u3714 = KTree.node A10K2.u3710 (nat_lit 59943198) (nat_lit 9778753158) (nat_lit 0) A10K2.u3713 from rfl, allE_node, arows3710, irow3714, arows3713]
  all_goals rfl

theorem atot3714 : totK PA10K2 A10K2.u3714 = [0, 295989007569, 4563037154741, 13849476035176, 14166082888563, 4381754165573, 426208662832, 6354482628, 0, 0] := by
  rw [show A10K2.u3714 = KTree.node A10K2.u3710 (nat_lit 59943198) (nat_lit 9778753158) (nat_lit 0) A10K2.u3713 from rfl, totK_node, atot3710, atot3713]
  decide +kernel

theorem arows3721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3721 = true := by
  rw [show A10K2.u3721 = KTree.node A10K2.u3717 (nat_lit 60051890) (nat_lit 11933677) (nat_lit 0) A10K2.u3720 from rfl, allE_node, arows3717, irow3721, arows3720]
  all_goals rfl

theorem atot3721 : totK PA10K2 A10K2.u3721 = [0, 0, 2317236486771, 10635258808512, 15884673744688, 8074884619508, 1273347637674, 62907382787, 0, 0] := by
  rw [show A10K2.u3721 = KTree.node A10K2.u3717 (nat_lit 60051890) (nat_lit 11933677) (nat_lit 0) A10K2.u3720 from rfl, totK_node, atot3717, atot3720]
  decide +kernel

theorem arows3729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3729 = true := by
  rw [show A10K2.u3729 = KTree.node A10K2.u3725 (nat_lit 60124407) (nat_lit 14712644156) (nat_lit 0) A10K2.u3728 from rfl, allE_node, arows3725, irow3729, arows3728]
  all_goals rfl

theorem atot3729 : totK PA10K2 A10K2.u3729 = [0, 0, 2272510662827, 10232022031813, 15751350983725, 8511976256616, 1326518447856, 49110149083, 0, 0] := by
  rw [show A10K2.u3729 = KTree.node A10K2.u3725 (nat_lit 60124407) (nat_lit 14712644156) (nat_lit 0) A10K2.u3728 from rfl, totK_node, atot3725, atot3728]
  decide +kernel

theorem arows3736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3736 = true := by
  rw [show A10K2.u3736 = KTree.node A10K2.u3732 (nat_lit 60181005) (nat_lit 5801448251) (nat_lit 0) A10K2.u3735 from rfl, allE_node, arows3732, irow3736, arows3735]
  all_goals rfl

theorem atot3736 : totK PA10K2 A10K2.u3736 = [0, 0, 1301340303726, 8259214530038, 15879709449321, 10093084463609, 1900368418240, 100242062403, 0, 0] := by
  rw [show A10K2.u3736 = KTree.node A10K2.u3732 (nat_lit 60181005) (nat_lit 5801448251) (nat_lit 0) A10K2.u3735 from rfl, totK_node, atot3732, atot3735]
  decide +kernel

theorem arows3745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3745 = true := by
  rw [show A10K2.u3745 = KTree.node A10K2.u3741 (nat_lit 60820948) (nat_lit 11933677) (nat_lit 0) A10K2.u3744 from rfl, allE_node, arows3741, irow3745, arows3744]
  all_goals rfl

theorem atot3745 : totK PA10K2 A10K2.u3745 = [0, 0, 1585054149079, 8074814470067, 14387857937458, 10230557927631, 2933693706935, 346555620032, 6354482628, 0] := by
  rw [show A10K2.u3745 = KTree.node A10K2.u3741 (nat_lit 60820948) (nat_lit 11933677) (nat_lit 0) A10K2.u3744 from rfl, totK_node, atot3741, atot3744]
  decide +kernel

theorem arows3752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3752 = true := by
  rw [show A10K2.u3752 = KTree.node A10K2.u3748 (nat_lit 60866600) (nat_lit 12782016780) (nat_lit 0) A10K2.u3751 from rfl, allE_node, arows3748, irow3752, arows3751]
  all_goals rfl

theorem atot3752 : totK PA10K2 A10K2.u3752 = [0, 0, 1129612411836, 6558721212931, 14584946500833, 12994022561919, 3450454478327, 288839238509, 5546304973, 0] := by
  rw [show A10K2.u3752 = KTree.node A10K2.u3748 (nat_lit 60866600) (nat_lit 12782016780) (nat_lit 0) A10K2.u3751 from rfl, totK_node, atot3748, atot3751]
  decide +kernel

theorem arows3760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3760 = true := by
  rw [show A10K2.u3760 = KTree.node A10K2.u3756 (nat_lit 60963610) (nat_lit 12757025019) (nat_lit 0) A10K2.u3759 from rfl, allE_node, arows3756, irow3760, arows3759]
  all_goals rfl

theorem atot3760 : totK PA10K2 A10K2.u3760 = [0, 0, 1606041694478, 8911978097963, 15839335226941, 9865328015659, 1693932239937, 80601872196, 0, 0] := by
  rw [show A10K2.u3760 = KTree.node A10K2.u3756 (nat_lit 60963610) (nat_lit 12757025019) (nat_lit 0) A10K2.u3759 from rfl, totK_node, atot3756, atot3759]
  decide +kernel

theorem arows3767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3767 = true := by
  rw [show A10K2.u3767 = KTree.node A10K2.u3763 (nat_lit 61416685) (nat_lit 5890118319) (nat_lit 0) A10K2.u3766 from rfl, allE_node, arows3763, irow3767, arows3766]
  all_goals rfl

theorem atot3767 : totK PA10K2 A10K2.u3767 = [0, 0, 1317434247939, 7154572504699, 14436235211347, 11909339327220, 3144150608999, 289529914710, 6354482628, 0] := by
  rw [show A10K2.u3767 = KTree.node A10K2.u3763 (nat_lit 61416685) (nat_lit 5890118319) (nat_lit 0) A10K2.u3766 from rfl, totK_node, atot3763, atot3766]
  decide +kernel

theorem arows3777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3777 = true := by
  rw [show A10K2.u3777 = KTree.node A10K2.u3773 (nat_lit 61439486) (nat_lit 15941591276) (nat_lit 0) A10K2.u3776 from rfl, allE_node, arows3773, irow3777, arows3776]
  all_goals rfl

theorem atot3777 : totK PA10K2 A10K2.u3777 = [0, 0, 980831852906, 6379353623038, 14079938163635, 12600740060952, 4394976246945, 647386399544, 31082886609, 0] := by
  rw [show A10K2.u3777 = KTree.node A10K2.u3773 (nat_lit 61439486) (nat_lit 15941591276) (nat_lit 0) A10K2.u3776 from rfl, totK_node, atot3773, atot3776]
  decide +kernel

theorem arows3784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3784 = true := by
  rw [show A10K2.u3784 = KTree.node A10K2.u3780 (nat_lit 61475618) (nat_lit 11977706767) (nat_lit 0) A10K2.u3783 from rfl, allE_node, arows3780, irow3784, arows3783]
  all_goals rfl

theorem atot3784 : totK PA10K2 A10K2.u3784 = [0, 0, 1401585845181, 7232938668243, 14087366026420, 11827384210776, 3602844738533, 326960654476, 6121173289, 0] := by
  rw [show A10K2.u3784 = KTree.node A10K2.u3780 (nat_lit 61475618) (nat_lit 11977706767) (nat_lit 0) A10K2.u3783 from rfl, totK_node, atot3780, atot3783]
  decide +kernel

theorem arows3792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3792 = true := by
  rw [show A10K2.u3792 = KTree.node A10K2.u3788 (nat_lit 61515259) (nat_lit 6243784505) (nat_lit 0) A10K2.u3791 from rfl, allE_node, arows3788, irow3792, arows3791]
  all_goals rfl

theorem atot3792 : totK PA10K2 A10K2.u3792 = [0, 0, 916737951006, 6070831416117, 14070787498993, 12612130863153, 3576903584679, 323630066971, 6354482628, 0] := by
  rw [show A10K2.u3792 = KTree.node A10K2.u3788 (nat_lit 61515259) (nat_lit 6243784505) (nat_lit 0) A10K2.u3791 from rfl, totK_node, atot3788, atot3791]
  decide +kernel

theorem arows3799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3799 = true := by
  rw [show A10K2.u3799 = KTree.node A10K2.u3795 (nat_lit 61566459) (nat_lit 6230449794) (nat_lit 0) A10K2.u3798 from rfl, allE_node, arows3795, irow3799, arows3798]
  all_goals rfl

theorem atot3799 : totK PA10K2 A10K2.u3799 = [0, 0, 1407657353788, 7906344671016, 15355870942606, 12014152002649, 3497756013703, 352178905235, 7047025452, 0] := by
  rw [show A10K2.u3799 = KTree.node A10K2.u3795 (nat_lit 61566459) (nat_lit 6230449794) (nat_lit 0) A10K2.u3798 from rfl, totK_node, atot3795, atot3798]
  decide +kernel

theorem arows3808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3808 = true := by
  rw [show A10K2.u3808 = KTree.node A10K2.u3804 (nat_lit 61872483) (nat_lit 8592233008) (nat_lit 0) A10K2.u3807 from rfl, allE_node, arows3804, irow3808, arows3807]
  all_goals rfl

theorem atot3808 : totK PA10K2 A10K2.u3808 = [0, 0, 1806013987253, 9257490568299, 15749993250369, 9880116405933, 2077793185592, 121003491821, 0, 0] := by
  rw [show A10K2.u3808 = KTree.node A10K2.u3804 (nat_lit 61872483) (nat_lit 8592233008) (nat_lit 0) A10K2.u3807 from rfl, totK_node, atot3804, atot3807]
  decide +kernel

theorem arows3815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3815 = true := by
  rw [show A10K2.u3815 = KTree.node A10K2.u3811 (nat_lit 61923725) (nat_lit 3053374602) (nat_lit 32) A10K2.u3814 from rfl, allE_node, arows3811, irow3815, arows3814]
  all_goals rfl

theorem atot3815 : totK PA10K2 A10K2.u3815 = [0, 0, 1296775117300, 6969704307889, 14319655232764, 12125129122087, 3165064136344, 286909149428, 5546304973, 0] := by
  rw [show A10K2.u3815 = KTree.node A10K2.u3811 (nat_lit 61923725) (nat_lit 3053374602) (nat_lit 32) A10K2.u3814 from rfl, totK_node, atot3811, atot3814]
  decide +kernel

theorem arows3823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3823 = true := by
  rw [show A10K2.u3823 = KTree.node A10K2.u3819 (nat_lit 61973915) (nat_lit 9868030166) (nat_lit 0) A10K2.u3822 from rfl, allE_node, arows3819, irow3823, arows3822]
  all_goals rfl

theorem atot3823 : totK PA10K2 A10K2.u3823 = [0, 0, 800788206144, 6082693324849, 14454116248544, 12782777805000, 4072209045067, 535755336906, 30647824416, 0] := by
  rw [show A10K2.u3823 = KTree.node A10K2.u3819 (nat_lit 61973915) (nat_lit 9868030166) (nat_lit 0) A10K2.u3822 from rfl, totK_node, atot3819, atot3822]
  decide +kernel

theorem arows3830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3830 = true := by
  rw [show A10K2.u3830 = KTree.node A10K2.u3826 (nat_lit 62003200) (nat_lit 15368788893) (nat_lit 0) A10K2.u3829 from rfl, allE_node, arows3826, irow3830, arows3829]
  all_goals rfl

theorem atot3830 : totK PA10K2 A10K2.u3830 = [0, 0, 1708570666615, 8116516878704, 14070550499193, 10587001357816, 3065620760329, 308752525880, 6121173289, 0] := by
  rw [show A10K2.u3830 = KTree.node A10K2.u3826 (nat_lit 62003200) (nat_lit 15368788893) (nat_lit 0) A10K2.u3829 from rfl, totK_node, atot3826, atot3829]
  decide +kernel

theorem arows3842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3842 = true := by
  rw [show A10K2.u3842 = KTree.node A10K2.u3838 (nat_lit 62039536) (nat_lit 3411521629) (nat_lit 0) A10K2.u3841 from rfl, allE_node, arows3838, irow3842, arows3841]
  all_goals rfl

theorem atot3842 : totK PA10K2 A10K2.u3842 = [0, 0, 582523478866, 5392220639012, 14143446269215, 13268570105361, 3834799760500, 393289894780, 6354482628, 0] := by
  rw [show A10K2.u3842 = KTree.node A10K2.u3838 (nat_lit 62039536) (nat_lit 3411521629) (nat_lit 0) A10K2.u3841 from rfl, totK_node, atot3838, atot3841]
  decide +kernel

theorem arows3849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3849 = true := by
  rw [show A10K2.u3849 = KTree.node A10K2.u3845 (nat_lit 62149062) (nat_lit 12521717000) (nat_lit 8) A10K2.u3848 from rfl, allE_node, arows3845, irow3849, arows3848]
  all_goals rfl

theorem atot3849 : totK PA10K2 A10K2.u3849 = [0, 0, 0, 2495368681122, 11443244597100, 16084122421323, 6944651877337, 989257619719, 42819180159, 0] := by
  rw [show A10K2.u3849 = KTree.node A10K2.u3845 (nat_lit 62149062) (nat_lit 12521717000) (nat_lit 8) A10K2.u3848 from rfl, totK_node, atot3845, atot3848]
  decide +kernel

theorem arows3857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3857 = true := by
  rw [show A10K2.u3857 = KTree.node A10K2.u3853 (nat_lit 62259788) (nat_lit 10628472875) (nat_lit 0) A10K2.u3856 from rfl, allE_node, arows3853, irow3857, arows3856]
  all_goals rfl

theorem atot3857 : totK PA10K2 A10K2.u3857 = [0, 0, 0, 2716018112348, 11792604001742, 15885223672842, 6492449183589, 862369776674, 36784204646, 0] := by
  rw [show A10K2.u3857 = KTree.node A10K2.u3853 (nat_lit 62259788) (nat_lit 10628472875) (nat_lit 0) A10K2.u3856 from rfl, totK_node, atot3853, atot3856]
  decide +kernel

theorem arows3864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3864 = true := by
  rw [show A10K2.u3864 = KTree.node A10K2.u3860 (nat_lit 62294307) (nat_lit 9666341021) (nat_lit 0) A10K2.u3863 from rfl, allE_node, arows3860, irow3864, arows3863]
  all_goals rfl

theorem atot3864 : totK PA10K2 A10K2.u3864 = [0, 0, 0, 840803844797, 6390945584320, 14939189372818, 11579083109973, 2896492729049, 174269357125, 0] := by
  rw [show A10K2.u3864 = KTree.node A10K2.u3860 (nat_lit 62294307) (nat_lit 9666341021) (nat_lit 0) A10K2.u3863 from rfl, totK_node, atot3860, atot3863]
  decide +kernel

theorem arows3873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3873 = true := by
  rw [show A10K2.u3873 = KTree.node A10K2.u3869 (nat_lit 62933101) (nat_lit 5512705346) (nat_lit 0) A10K2.u3872 from rfl, allE_node, arows3869, irow3873, arows3872]
  all_goals rfl

theorem atot3873 : totK PA10K2 A10K2.u3873 = [0, 2205856923078, 10257751039817, 15765318135735, 8625343641395, 1417439085936, 280066488618, 429542201963, 142269073820, 6354482628] := by
  rw [show A10K2.u3873 = KTree.node A10K2.u3869 (nat_lit 62933101) (nat_lit 5512705346) (nat_lit 0) A10K2.u3872 from rfl, totK_node, atot3869, atot3872]
  decide +kernel

theorem arows3880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3880 = true := by
  rw [show A10K2.u3880 = KTree.node A10K2.u3876 (nat_lit 62965816) (nat_lit 13900348188) (nat_lit 0) A10K2.u3879 from rfl, allE_node, arows3876, irow3880, arows3879]
  all_goals rfl

theorem atot3880 : totK PA10K2 A10K2.u3880 = [0, 783941292525, 5368824005828, 13278019779092, 13683077076201, 5278990663150, 734718782301, 30650496230, 0, 0] := by
  rw [show A10K2.u3880 = KTree.node A10K2.u3876 (nat_lit 62965816) (nat_lit 13900348188) (nat_lit 0) A10K2.u3879 from rfl, totK_node, atot3876, atot3879]
  decide +kernel

theorem arows3888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3888 = true := by
  rw [show A10K2.u3888 = KTree.node A10K2.u3884 (nat_lit 63137686) (nat_lit 15725098054) (nat_lit 0) A10K2.u3887 from rfl, allE_node, arows3884, irow3888, arows3887]
  all_goals rfl

theorem atot3888 : totK PA10K2 A10K2.u3888 = [0, 1461308260998, 8097467802781, 15667969810784, 11796415094583, 2865400503266, 151889841826, 0, 0, 0] := by
  rw [show A10K2.u3888 = KTree.node A10K2.u3884 (nat_lit 63137686) (nat_lit 15725098054) (nat_lit 0) A10K2.u3887 from rfl, totK_node, atot3884, atot3887]
  decide +kernel

theorem arows3895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3895 = true := by
  rw [show A10K2.u3895 = KTree.node A10K2.u3891 (nat_lit 63170239) (nat_lit 12309121275) (nat_lit 0) A10K2.u3894 from rfl, allE_node, arows3891, irow3895, arows3894]
  all_goals rfl

theorem atot3895 : totK PA10K2 A10K2.u3895 = [0, 0, 2304192350869, 10485648484459, 15996644859904, 9147049756572, 1635601374767, 75062079822, 0, 0] := by
  rw [show A10K2.u3895 = KTree.node A10K2.u3891 (nat_lit 63170239) (nat_lit 12309121275) (nat_lit 0) A10K2.u3894 from rfl, totK_node, atot3891, atot3894]
  decide +kernel

theorem arows3905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3905 = true := by
  rw [show A10K2.u3905 = KTree.node A10K2.u3901 (nat_lit 63202116) (nat_lit 12038350636) (nat_lit 0) A10K2.u3904 from rfl, allE_node, arows3901, irow3905, arows3904]
  all_goals rfl

theorem atot3905 : totK PA10K2 A10K2.u3905 = [0, 0, 1361137082739, 8180866747778, 16040117167900, 11041234483643, 2264224361492, 109585587515, 0, 0] := by
  rw [show A10K2.u3905 = KTree.node A10K2.u3901 (nat_lit 63202116) (nat_lit 12038350636) (nat_lit 0) A10K2.u3904 from rfl, totK_node, atot3901, atot3904]
  decide +kernel

theorem arows3912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3912 = true := by
  rw [show A10K2.u3912 = KTree.node A10K2.u3908 (nat_lit 63374189) (nat_lit 5387155054) (nat_lit 0) A10K2.u3911 from rfl, allE_node, arows3908, irow3912, arows3911]
  all_goals rfl

theorem atot3912 : totK PA10K2 A10K2.u3912 = [0, 0, 1378234521411, 7653385088323, 14936152566566, 11785482472569, 3435897508299, 367176503616, 7903172220, 0] := by
  rw [show A10K2.u3912 = KTree.node A10K2.u3908 (nat_lit 63374189) (nat_lit 5387155054) (nat_lit 0) A10K2.u3911 from rfl, totK_node, atot3908, atot3911]
  decide +kernel

theorem arows3920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3920 = true := by
  rw [show A10K2.u3920 = KTree.node A10K2.u3916 (nat_lit 63514288) (nat_lit 9373637245) (nat_lit 0) A10K2.u3919 from rfl, allE_node, arows3916, irow3920, arows3919]
  all_goals rfl

theorem atot3920 : totK PA10K2 A10K2.u3920 = [0, 1505441007826, 7182237568978, 12733228537487, 11338887319888, 5488129701371, 1112258500264, 62368562949, 0, 0] := by
  rw [show A10K2.u3920 = KTree.node A10K2.u3916 (nat_lit 63514288) (nat_lit 9373637245) (nat_lit 0) A10K2.u3919 from rfl, totK_node, atot3916, atot3919]
  decide +kernel

theorem arows3927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3927 = true := by
  rw [show A10K2.u3927 = KTree.node A10K2.u3923 (nat_lit 63536868) (nat_lit 5401623740) (nat_lit 0) A10K2.u3926 from rfl, allE_node, arows3923, irow3927, arows3926]
  all_goals rfl

theorem atot3927 : totK PA10K2 A10K2.u3927 = [0, 800212678090, 5650154009004, 13699132394516, 13271569105433, 5039172000272, 705593868861, 31082886609, 0, 0] := by
  rw [show A10K2.u3927 = KTree.node A10K2.u3923 (nat_lit 63536868) (nat_lit 5401623740) (nat_lit 0) A10K2.u3926 from rfl, totK_node, atot3923, atot3926]
  decide +kernel

theorem arows3936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3936 = true := by
  rw [show A10K2.u3936 = KTree.node A10K2.u3932 (nat_lit 63580826) (nat_lit 14661001598) (nat_lit 0) A10K2.u3935 from rfl, allE_node, arows3932, irow3936, arows3935]
  all_goals rfl

theorem atot3936 : totK PA10K2 A10K2.u3936 = [0, 1538572446206, 8030048418425, 14566136586221, 11165252519449, 3377234877073, 318707853584, 6121173289, 0, 0] := by
  rw [show A10K2.u3936 = KTree.node A10K2.u3932 (nat_lit 63580826) (nat_lit 14661001598) (nat_lit 0) A10K2.u3935 from rfl, totK_node, atot3932, atot3935]
  decide +kernel

theorem arows3943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3943 = true := by
  rw [show A10K2.u3943 = KTree.node A10K2.u3939 (nat_lit 63625495) (nat_lit 6263324263) (nat_lit 0) A10K2.u3942 from rfl, allE_node, arows3939, irow3943, arows3942]
  all_goals rfl

theorem atot3943 : totK PA10K2 A10K2.u3943 = [0, 1360874852670, 7373817708145, 14715328051478, 12047017357541, 3316710668993, 286769339720, 6354482628, 0, 0] := by
  rw [show A10K2.u3943 = KTree.node A10K2.u3939 (nat_lit 63625495) (nat_lit 6263324263) (nat_lit 0) A10K2.u3942 from rfl, totK_node, atot3939, atot3942]
  decide +kernel

theorem arows3951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3951 = true := by
  rw [show A10K2.u3951 = KTree.node A10K2.u3947 (nat_lit 63667257) (nat_lit 7244271112) (nat_lit 0) A10K2.u3950 from rfl, allE_node, arows3947, irow3951, arows3950]
  all_goals rfl

theorem atot3951 : totK PA10K2 A10K2.u3951 = [0, 862423573369, 6067133411663, 14380187502496, 13499992533587, 4547473032956, 427744992521, 6904928264, 0, 0] := by
  rw [show A10K2.u3951 = KTree.node A10K2.u3947 (nat_lit 63667257) (nat_lit 7244271112) (nat_lit 0) A10K2.u3950 from rfl, totK_node, atot3947, atot3950]
  decide +kernel

theorem arows3958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3958 = true := by
  rw [show A10K2.u3958 = KTree.node A10K2.u3954 (nat_lit 63700001) (nat_lit 8486237835) (nat_lit 0) A10K2.u3957 from rfl, allE_node, arows3954, irow3958, arows3957]
  all_goals rfl

theorem atot3958 : totK PA10K2 A10K2.u3958 = [0, 0, 1808843992720, 9304061990765, 15976374566259, 10104722463931, 1973387723146, 99925900411, 0, 0] := by
  rw [show A10K2.u3958 = KTree.node A10K2.u3954 (nat_lit 63700001) (nat_lit 8486237835) (nat_lit 0) A10K2.u3957 from rfl, totK_node, atot3954, atot3957]
  decide +kernel

theorem arows3969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3969 = true := by
  rw [show A10K2.u3969 = KTree.node A10K2.u3965 (nat_lit 63796439) (nat_lit 12564836017) (nat_lit 0) A10K2.u3968 from rfl, allE_node, arows3965, irow3969, arows3968]
  all_goals rfl

theorem atot3969 : totK PA10K2 A10K2.u3969 = [0, 0, 1356567296292, 7253282042833, 14071049643358, 11527788880830, 4082405631735, 611924525855, 31018567651, 0] := by
  rw [show A10K2.u3969 = KTree.node A10K2.u3965 (nat_lit 63796439) (nat_lit 12564836017) (nat_lit 0) A10K2.u3968 from rfl, totK_node, atot3965, atot3968]
  decide +kernel

theorem arows3976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3976 = true := by
  rw [show A10K2.u3976 = KTree.node A10K2.u3972 (nat_lit 63842012) (nat_lit 10859328874) (nat_lit 0) A10K2.u3975 from rfl, allE_node, arows3972, irow3976, arows3975]
  all_goals rfl

theorem atot3976 : totK PA10K2 A10K2.u3976 = [0, 0, 1538105511236, 7898075748455, 14403076520963, 11242837822326, 3413973375167, 338170264305, 5685526223, 0] := by
  rw [show A10K2.u3976 = KTree.node A10K2.u3972 (nat_lit 63842012) (nat_lit 10859328874) (nat_lit 0) A10K2.u3975 from rfl, totK_node, atot3972, atot3975]
  decide +kernel

theorem arows3984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3984 = true := by
  rw [show A10K2.u3984 = KTree.node A10K2.u3980 (nat_lit 63885672) (nat_lit 9644858716) (nat_lit 0) A10K2.u3983 from rfl, allE_node, arows3980, irow3984, arows3983]
  all_goals rfl

theorem atot3984 : totK PA10K2 A10K2.u3984 = [0, 0, 1360384191650, 7473096045881, 14771799222365, 11775870963911, 3106885020461, 279066551788, 6239673734, 0] := by
  rw [show A10K2.u3984 = KTree.node A10K2.u3980 (nat_lit 63885672) (nat_lit 9644858716) (nat_lit 0) A10K2.u3983 from rfl, totK_node, atot3980, atot3983]
  decide +kernel

theorem arows3991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3991 = true := by
  rw [show A10K2.u3991 = KTree.node A10K2.u3987 (nat_lit 63927586) (nat_lit 13609888108) (nat_lit 0) A10K2.u3990 from rfl, allE_node, arows3987, irow3991, arows3990]
  all_goals rfl

theorem atot3991 : totK PA10K2 A10K2.u3991 = [0, 887742285343, 4746795729738, 10916059089859, 13298093057507, 7913865320395, 1696587633048, 93667527727, 0, 0] := by
  rw [show A10K2.u3991 = KTree.node A10K2.u3987 (nat_lit 63927586) (nat_lit 13609888108) (nat_lit 0) A10K2.u3990 from rfl, totK_node, atot3987, atot3990]
  decide +kernel

theorem arows4000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4000 = true := by
  rw [show A10K2.u4000 = KTree.node A10K2.u3996 (nat_lit 64520200) (nat_lit 14576044548) (nat_lit 0) A10K2.u3999 from rfl, allE_node, arows3996, irow4000, arows3999]
  all_goals rfl

theorem atot4000 : totK PA10K2 A10K2.u4000 = [0, 982976898703, 6178056027803, 13867562231477, 13211019441964, 4806805405859, 584930733699, 13364899180, 0, 0] := by
  rw [show A10K2.u4000 = KTree.node A10K2.u3996 (nat_lit 64520200) (nat_lit 14576044548) (nat_lit 0) A10K2.u3999 from rfl, totK_node, atot3996, atot3999]
  decide +kernel

theorem arows4007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4007 = true := by
  rw [show A10K2.u4007 = KTree.node A10K2.u4003 (nat_lit 64568712) (nat_lit 11978594253) (nat_lit 0) A10K2.u4006 from rfl, allE_node, arows4003, irow4007, arows4006]
  all_goals rfl

theorem atot4007 : totK PA10K2 A10K2.u4007 = [0, 2133734795744, 10031603624152, 15937161626083, 9661380677944, 1982327417561, 102526105975, 0, 0, 0] := by
  rw [show A10K2.u4007 = KTree.node A10K2.u4003 (nat_lit 64568712) (nat_lit 11978594253) (nat_lit 0) A10K2.u4006 from rfl, totK_node, atot4003, atot4006]
  decide +kernel

theorem arows4015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4015 = true := by
  rw [show A10K2.u4015 = KTree.node A10K2.u4011 (nat_lit 64601592) (nat_lit 8308570419) (nat_lit 0) A10K2.u4014 from rfl, allE_node, arows4011, irow4015, arows4014]
  all_goals rfl

theorem atot4015 : totK PA10K2 A10K2.u4015 = [0, 383428828220, 3833884519822, 12163050658840, 15088769396597, 6681862542609, 952383563174, 37204059898, 0, 0] := by
  rw [show A10K2.u4015 = KTree.node A10K2.u4011 (nat_lit 64601592) (nat_lit 8308570419) (nat_lit 0) A10K2.u4014 from rfl, totK_node, atot4011, atot4014]
  decide +kernel

theorem arows4022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4022 = true := by
  rw [show A10K2.u4022 = KTree.node A10K2.u4018 (nat_lit 64698092) (nat_lit 10585170875) (nat_lit 0) A10K2.u4021 from rfl, allE_node, arows4018, irow4022, arows4021]
  all_goals rfl

theorem atot4022 : totK PA10K2 A10K2.u4022 = [0, 2005576377732, 9886696654100, 16236635897833, 9678907374782, 1696402305419, 63696072410, 0, 0, 0] := by
  rw [show A10K2.u4022 = KTree.node A10K2.u4018 (nat_lit 64698092) (nat_lit 10585170875) (nat_lit 0) A10K2.u4021 from rfl, totK_node, atot4018, atot4021]
  decide +kernel

theorem arows4032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4032 = true := by
  rw [show A10K2.u4032 = KTree.node A10K2.u4028 (nat_lit 64728310) (nat_lit 16319387176) (nat_lit 0) A10K2.u4031 from rfl, allE_node, arows4028, irow4032, arows4031]
  all_goals rfl

theorem atot4032 : totK PA10K2 A10K2.u4032 = [0, 0, 2385679921159, 11141829575666, 16554753570374, 8189579324259, 1020139240750, 20018912194, 0, 0] := by
  rw [show A10K2.u4032 = KTree.node A10K2.u4028 (nat_lit 64728310) (nat_lit 16319387176) (nat_lit 0) A10K2.u4031 from rfl, totK_node, atot4028, atot4031]
  decide +kernel

theorem arows4039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4039 = true := by
  rw [show A10K2.u4039 = KTree.node A10K2.u4035 (nat_lit 64766412) (nat_lit 7394287599) (nat_lit 0) A10K2.u4038 from rfl, allE_node, arows4035, irow4039, arows4038]
  all_goals rfl

theorem atot4039 : totK PA10K2 A10K2.u4039 = [0, 0, 1868716557835, 9240393745622, 15810254549131, 10470979316747, 2320943010135, 130759883619, 0, 0] := by
  rw [show A10K2.u4039 = KTree.node A10K2.u4035 (nat_lit 64766412) (nat_lit 7394287599) (nat_lit 0) A10K2.u4038 from rfl, totK_node, atot4035, atot4038]
  decide +kernel

theorem arows4047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4047 = true := by
  rw [show A10K2.u4047 = KTree.node A10K2.u4043 (nat_lit 64810592) (nat_lit 12814510479) (nat_lit 0) A10K2.u4046 from rfl, allE_node, arows4043, irow4047, arows4046]
  all_goals rfl

theorem atot4047 : totK PA10K2 A10K2.u4047 = [0, 0, 1228023864193, 6823555294334, 14367950050343, 12791586171439, 3912218289861, 350342753728, 7007974415, 0] := by
  rw [show A10K2.u4047 = KTree.node A10K2.u4043 (nat_lit 64810592) (nat_lit 12814510479) (nat_lit 0) A10K2.u4046 from rfl, totK_node, atot4043, atot4046]
  decide +kernel

theorem arows4054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4054 = true := by
  rw [show A10K2.u4054 = KTree.node A10K2.u4050 (nat_lit 64847539) (nat_lit 9590655851) (nat_lit 0) A10K2.u4053 from rfl, allE_node, arows4050, irow4054, arows4053]
  all_goals rfl

theorem atot4054 : totK PA10K2 A10K2.u4054 = [0, 0, 903713312809, 6398133738838, 14660785470255, 13081483103694, 4217426807625, 416830389385, 7151180950, 0] := by
  rw [show A10K2.u4054 = KTree.node A10K2.u4050 (nat_lit 64847539) (nat_lit 9590655851) (nat_lit 0) A10K2.u4053 from rfl, totK_node, atot4050, atot4053]
  decide +kernel

theorem arows4063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4063 = true := by
  rw [show A10K2.u4063 = KTree.node A10K2.u4059 (nat_lit 64955747) (nat_lit 9381289585) (nat_lit 0) A10K2.u4062 from rfl, allE_node, arows4059, irow4063, arows4062]
  all_goals rfl

theorem atot4063 : totK PA10K2 A10K2.u4063 = [0, 0, 2386020461250, 10373739652916, 15530469418966, 9232083923532, 1842407994032, 86843019383, 0, 0] := by
  rw [show A10K2.u4063 = KTree.node A10K2.u4059 (nat_lit 64955747) (nat_lit 9381289585) (nat_lit 0) A10K2.u4062 from rfl, totK_node, atot4059, atot4062]
  decide +kernel

theorem arows4070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4070 = true := by
  rw [show A10K2.u4070 = KTree.node A10K2.u4066 (nat_lit 64983941) (nat_lit 4163399079) (nat_lit 0) A10K2.u4069 from rfl, allE_node, arows4066, irow4070, arows4069]
  all_goals rfl

theorem atot4070 : totK PA10K2 A10K2.u4070 = [0, 0, 0, 3364464276257, 13102852996688, 15999534954059, 6299397737484, 658963546981, 12758098799, 0] := by
  rw [show A10K2.u4070 = KTree.node A10K2.u4066 (nat_lit 64983941) (nat_lit 4163399079) (nat_lit 0) A10K2.u4069 from rfl, totK_node, atot4066, atot4069]
  decide +kernel

theorem arows4078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4078 = true := by
  rw [show A10K2.u4078 = KTree.node A10K2.u4074 (nat_lit 67112839) (nat_lit 14605439975) (nat_lit 0) A10K2.u4077 from rfl, allE_node, arows4074, irow4078, arows4077]
  all_goals rfl

theorem atot4078 : totK PA10K2 A10K2.u4078 = [1597148671271, 7408606953095, 11241558964431, 6064906819696, 2834890132268, 4539790368184, 3740560321955, 961189328672, 61018386929, 0] := by
  rw [show A10K2.u4078 = KTree.node A10K2.u4074 (nat_lit 67112839) (nat_lit 14605439975) (nat_lit 0) A10K2.u4077 from rfl, totK_node, atot4074, atot4077]
  decide +kernel

theorem arows4085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4085 = true := by
  rw [show A10K2.u4085 = KTree.node A10K2.u4081 (nat_lit 67144022) (nat_lit 2273532392) (nat_lit 0) A10K2.u4084 from rfl, allE_node, arows4081, irow4085, arows4084]
  all_goals rfl

theorem atot4085 : totK PA10K2 A10K2.u4085 = [741544312551, 5056769077638, 12845974647116, 13760690563064, 5363016560833, 713874974091, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4085 = KTree.node A10K2.u4081 (nat_lit 67144022) (nat_lit 2273532392) (nat_lit 0) A10K2.u4084 from rfl, totK_node, atot4081, atot4084]
  decide +kernel

theorem arows4101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4101 = true := by
  rw [show A10K2.u4101 = KTree.node A10K2.u4097 (nat_lit 67244534) (nat_lit 16077308316) (nat_lit 0) A10K2.u4100 from rfl, allE_node, arows4097, irow4101, arows4100]
  all_goals rfl

theorem atot4101 : totK PA10K2 A10K2.u4101 = [1857560860672, 8577711204526, 14325989392886, 10343039960395, 3017550656390, 291879019978, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4101 = KTree.node A10K2.u4097 (nat_lit 67244534) (nat_lit 16077308316) (nat_lit 0) A10K2.u4100 from rfl, totK_node, atot4097, atot4100]
  decide +kernel

theorem arows4108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4108 = true := by
  rw [show A10K2.u4108 = KTree.node A10K2.u4104 (nat_lit 67283725) (nat_lit 5814114857) (nat_lit 0) A10K2.u4107 from rfl, allE_node, arows4104, irow4108, arows4107]
  all_goals rfl

theorem atot4108 : totK PA10K2 A10K2.u4108 = [1008470200324, 6296448519846, 13860167358146, 12443504375335, 3883714026517, 393649271627, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4108 = KTree.node A10K2.u4104 (nat_lit 67283725) (nat_lit 5814114857) (nat_lit 0) A10K2.u4107 from rfl, totK_node, atot4104, atot4107]
  decide +kernel

theorem arows4116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4116 = true := by
  rw [show A10K2.u4116 = KTree.node A10K2.u4112 (nat_lit 67333781) (nat_lit 1990508179) (nat_lit 0) A10K2.u4115 from rfl, allE_node, arows4112, irow4116, arows4115]
  all_goals rfl

theorem atot4116 : totK PA10K2 A10K2.u4116 = [1078827900697, 7040238007911, 15100209313975, 12524892733537, 3849525303723, 382666954661, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4116 = KTree.node A10K2.u4112 (nat_lit 67333781) (nat_lit 1990508179) (nat_lit 0) A10K2.u4115 from rfl, totK_node, atot4112, atot4115]
  decide +kernel

theorem arows4123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4123 = true := by
  rw [show A10K2.u4123 = KTree.node A10K2.u4119 (nat_lit 67370061) (nat_lit 2370185312) (nat_lit 0) A10K2.u4122 from rfl, allE_node, arows4119, irow4123, arows4122]
  all_goals rfl

theorem atot4123 : totK PA10K2 A10K2.u4123 = [0, 2157610445060, 10061749186246, 15904085746389, 9378571337054, 1774726061908, 91941799992, 0, 0, 0] := by
  rw [show A10K2.u4123 = KTree.node A10K2.u4119 (nat_lit 67370061) (nat_lit 2370185312) (nat_lit 0) A10K2.u4122 from rfl, totK_node, atot4119, atot4122]
  decide +kernel

theorem arows4132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4132 = true := by
  rw [show A10K2.u4132 = KTree.node A10K2.u4128 (nat_lit 67400072) (nat_lit 14229919885) (nat_lit 0) A10K2.u4131 from rfl, allE_node, arows4128, irow4132, arows4131]
  all_goals rfl

theorem atot4132 : totK PA10K2 A10K2.u4132 = [0, 1254172466427, 7162590487332, 14018607184442, 11187553743482, 3850594761093, 593551555037, 30605747850, 0, 0] := by
  rw [show A10K2.u4132 = KTree.node A10K2.u4128 (nat_lit 67400072) (nat_lit 14229919885) (nat_lit 0) A10K2.u4131 from rfl, totK_node, atot4128, atot4131]
  decide +kernel

theorem arows4139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4139 = true := by
  rw [show A10K2.u4139 = KTree.node A10K2.u4135 (nat_lit 67502470) (nat_lit 15249561628) (nat_lit 0) A10K2.u4138 from rfl, allE_node, arows4135, irow4139, arows4138]
  all_goals rfl

theorem atot4139 : totK PA10K2 A10K2.u4139 = [0, 1266431997466, 7216947830644, 14336635797875, 11587935336916, 3364651137167, 325318369282, 5528811039, 0, 0] := by
  rw [show A10K2.u4139 = KTree.node A10K2.u4135 (nat_lit 67502470) (nat_lit 15249561628) (nat_lit 0) A10K2.u4138 from rfl, totK_node, atot4135, atot4138]
  decide +kernel

theorem arows4147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4147 = true := by
  rw [show A10K2.u4147 = KTree.node A10K2.u4143 (nat_lit 67537444) (nat_lit 13558446609) (nat_lit 0) A10K2.u4146 from rfl, allE_node, arows4143, irow4147, arows4146]
  all_goals rfl

theorem atot4147 : totK PA10K2 A10K2.u4147 = [0, 1097750996362, 6513722655954, 14157460950623, 12027869384342, 3277250365440, 280107429463, 5676195732, 0, 0] := by
  rw [show A10K2.u4147 = KTree.node A10K2.u4143 (nat_lit 67537444) (nat_lit 13558446609) (nat_lit 0) A10K2.u4146 from rfl, totK_node, atot4143, atot4146]
  decide +kernel

theorem arows4154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4154 = true := by
  rw [show A10K2.u4154 = KTree.node A10K2.u4150 (nat_lit 67593374) (nat_lit 14941068844) (nat_lit 0) A10K2.u4153 from rfl, allE_node, arows4150, irow4154, arows4153]
  all_goals rfl

theorem atot4154 : totK PA10K2 A10K2.u4154 = [833436429740, 4301569579445, 10563941374492, 14123267463797, 8229375910127, 1648189414336, 87681911118, 0, 0, 0] := by
  rw [show A10K2.u4154 = KTree.node A10K2.u4150 (nat_lit 67593374) (nat_lit 14941068844) (nat_lit 0) A10K2.u4153 from rfl, totK_node, atot4150, atot4153]
  decide +kernel

theorem arows4164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4164 = true := by
  rw [show A10K2.u4164 = KTree.node A10K2.u4160 (nat_lit 68180210) (nat_lit 10405505553) (nat_lit 0) A10K2.u4163 from rfl, allE_node, arows4160, irow4164, arows4163]
  all_goals rfl

theorem atot4164 : totK PA10K2 A10K2.u4164 = [1322336744556, 8109878236500, 15843036326125, 10855595203229, 2218312023114, 117958807809, 0, 0, 0, 0] := by
  rw [show A10K2.u4164 = KTree.node A10K2.u4160 (nat_lit 68180210) (nat_lit 10405505553) (nat_lit 0) A10K2.u4163 from rfl, totK_node, atot4160, atot4163]
  decide +kernel

theorem arows4171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4171 = true := by
  rw [show A10K2.u4171 = KTree.node A10K2.u4167 (nat_lit 68213522) (nat_lit 12670591423) (nat_lit 0) A10K2.u4170 from rfl, allE_node, arows4167, irow4171, arows4170]
  all_goals rfl

theorem atot4171 : totK PA10K2 A10K2.u4171 = [762984113060, 4868521805553, 12133639777103, 13746610662465, 6024181708312, 876279582971, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u4171 = KTree.node A10K2.u4167 (nat_lit 68213522) (nat_lit 12670591423) (nat_lit 0) A10K2.u4170 from rfl, totK_node, atot4167, atot4170]
  decide +kernel

theorem arows4179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4179 = true := by
  rw [show A10K2.u4179 = KTree.node A10K2.u4175 (nat_lit 68267671) (nat_lit 13918877224) (nat_lit 0) A10K2.u4178 from rfl, allE_node, arows4175, irow4179, arows4178]
  all_goals rfl

theorem atot4179 : totK PA10K2 A10K2.u4179 = [779393338859, 5149656934310, 12543551395771, 13342308716000, 5749693415139, 861963557860, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4179 = KTree.node A10K2.u4175 (nat_lit 68267671) (nat_lit 13918877224) (nat_lit 0) A10K2.u4178 from rfl, totK_node, atot4175, atot4178]
  decide +kernel

theorem arows4186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4186 = true := by
  rw [show A10K2.u4186 = KTree.node A10K2.u4182 (nat_lit 68299949) (nat_lit 6282078157) (nat_lit 0) A10K2.u4185 from rfl, allE_node, arows4182, irow4186, arows4185]
  all_goals rfl

theorem atot4186 : totK PA10K2 A10K2.u4186 = [2254086870602, 10446842373092, 15808156762671, 8391505123242, 1380149377440, 62600422739, 0, 0, 0, 0] := by
  rw [show A10K2.u4186 = KTree.node A10K2.u4182 (nat_lit 68299949) (nat_lit 6282078157) (nat_lit 0) A10K2.u4185 from rfl, totK_node, atot4182, atot4185]
  decide +kernel

theorem arows4195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4195 = true := by
  rw [show A10K2.u4195 = KTree.node A10K2.u4191 (nat_lit 68339543) (nat_lit 4395773119) (nat_lit 0) A10K2.u4194 from rfl, allE_node, arows4191, irow4195, arows4194]
  all_goals rfl

theorem atot4195 : totK PA10K2 A10K2.u4195 = [0, 3079781662818, 12526724897191, 15602016428220, 6013885811809, 783539664525, 31725663621, 0, 0, 0] := by
  rw [show A10K2.u4195 = KTree.node A10K2.u4191 (nat_lit 68339543) (nat_lit 4395773119) (nat_lit 0) A10K2.u4194 from rfl, totK_node, atot4191, atot4194]
  decide +kernel

theorem arows4202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4202 = true := by
  rw [show A10K2.u4202 = KTree.node A10K2.u4198 (nat_lit 68447245) (nat_lit 5166133133) (nat_lit 0) A10K2.u4201 from rfl, allE_node, arows4198, irow4202, arows4201]
  all_goals rfl

theorem atot4202 : totK PA10K2 A10K2.u4202 = [0, 2084714441917, 10045668755264, 15999578178729, 8986798431890, 1450286274960, 50107590360, 0, 0, 0] := by
  rw [show A10K2.u4202 = KTree.node A10K2.u4198 (nat_lit 68447245) (nat_lit 5166133133) (nat_lit 0) A10K2.u4201 from rfl, totK_node, atot4198, atot4201]
  decide +kernel

theorem arows4210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4210 = true := by
  rw [show A10K2.u4210 = KTree.node A10K2.u4206 (nat_lit 68553785) (nat_lit 7281133814) (nat_lit 0) A10K2.u4209 from rfl, allE_node, arows4206, irow4210, arows4209]
  all_goals rfl

theorem atot4210 : totK PA10K2 A10K2.u4210 = [0, 2192952428418, 10297761041736, 15874015812524, 8430417729797, 1361710302431, 67432810860, 0, 0, 0] := by
  rw [show A10K2.u4210 = KTree.node A10K2.u4206 (nat_lit 68553785) (nat_lit 7281133814) (nat_lit 0) A10K2.u4209 from rfl, totK_node, atot4206, atot4209]
  decide +kernel

theorem arows4217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4217 = true := by
  rw [show A10K2.u4217 = KTree.node A10K2.u4213 (nat_lit 68586502) (nat_lit 14379230333) (nat_lit 0) A10K2.u4216 from rfl, allE_node, arows4213, irow4217, arows4216]
  all_goals rfl

theorem atot4217 : totK PA10K2 A10K2.u4217 = [0, 835897603759, 6091673741150, 14266540129570, 12265387803171, 3513673467348, 293422010344, 0, 0, 0] := by
  rw [show A10K2.u4217 = KTree.node A10K2.u4213 (nat_lit 68586502) (nat_lit 14379230333) (nat_lit 0) A10K2.u4216 from rfl, totK_node, atot4213, atot4216]
  decide +kernel

theorem arows4228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4228 = true := by
  rw [show A10K2.u4228 = KTree.node A10K2.u4224 (nat_lit 68700456) (nat_lit 12023766111) (nat_lit 0) A10K2.u4227 from rfl, allE_node, arows4224, irow4228, arows4227]
  all_goals rfl

theorem atot4228 : totK PA10K2 A10K2.u4228 = [2205441570080, 10268336007511, 16033908595096, 9091906174775, 1534717025514, 144840701191, 84918787380, 6354482628, 0, 0] := by
  rw [show A10K2.u4228 = KTree.node A10K2.u4224 (nat_lit 68700456) (nat_lit 12023766111) (nat_lit 0) A10K2.u4227 from rfl, totK_node, atot4224, atot4227]
  decide +kernel

theorem arows4235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4235 = true := by
  rw [show A10K2.u4235 = KTree.node A10K2.u4231 (nat_lit 68733083) (nat_lit 9875192451) (nat_lit 0) A10K2.u4234 from rfl, allE_node, arows4231, irow4235, arows4234]
  all_goals rfl

theorem atot4235 : totK PA10K2 A10K2.u4235 = [780629253406, 4676515584296, 11861474761588, 14106318108600, 6417028134749, 926045434548, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u4235 = KTree.node A10K2.u4231 (nat_lit 68733083) (nat_lit 9875192451) (nat_lit 0) A10K2.u4234 from rfl, totK_node, atot4231, atot4234]
  decide +kernel

theorem arows4243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4243 = true := by
  rw [show A10K2.u4243 = KTree.node A10K2.u4239 (nat_lit 68903360) (nat_lit 15203328423) (nat_lit 0) A10K2.u4242 from rfl, allE_node, arows4239, irow4243, arows4242]
  all_goals rfl

theorem atot4243 : totK PA10K2 A10K2.u4243 = [1463230794992, 8465522673338, 16101481217057, 11282041118387, 2525767953902, 144789375420, 0, 0, 0, 0] := by
  rw [show A10K2.u4243 = KTree.node A10K2.u4239 (nat_lit 68903360) (nat_lit 15203328423) (nat_lit 0) A10K2.u4242 from rfl, totK_node, atot4239, atot4242]
  decide +kernel

theorem arows4250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4250 = true := by
  rw [show A10K2.u4250 = KTree.node A10K2.u4246 (nat_lit 68935725) (nat_lit 4969908050) (nat_lit 0) A10K2.u4249 from rfl, allE_node, arows4246, irow4250, arows4249]
  all_goals rfl

theorem atot4250 : totK PA10K2 A10K2.u4250 = [0, 2081644349289, 10053449533272, 16257963847818, 9613479794851, 1713467134322, 75062079822, 0, 0, 0] := by
  rw [show A10K2.u4250 = KTree.node A10K2.u4246 (nat_lit 68935725) (nat_lit 4969908050) (nat_lit 0) A10K2.u4249 from rfl, totK_node, atot4246, atot4249]
  decide +kernel

theorem arows4259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4259 = true := by
  rw [show A10K2.u4259 = KTree.node A10K2.u4255 (nat_lit 68966500) (nat_lit 13547978332) (nat_lit 0) A10K2.u4258 from rfl, allE_node, arows4255, irow4259, arows4258]
  all_goals rfl

theorem atot4259 : totK PA10K2 A10K2.u4259 = [0, 1890106142208, 9450550877514, 15962629596178, 9916190384185, 1964810957533, 98837276904, 0, 0, 0] := by
  rw [show A10K2.u4259 = KTree.node A10K2.u4255 (nat_lit 68966500) (nat_lit 13547978332) (nat_lit 0) A10K2.u4258 from rfl, totK_node, atot4255, atot4258]
  decide +kernel

theorem arows4266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4266 = true := by
  rw [show A10K2.u4266 = KTree.node A10K2.u4262 (nat_lit 69002654) (nat_lit 15508892991) (nat_lit 0) A10K2.u4265 from rfl, allE_node, arows4262, irow4266, arows4265]
  all_goals rfl

theorem atot4266 : totK PA10K2 A10K2.u4266 = [0, 1068376898294, 6285683856757, 13978841331647, 13108557423193, 4281891035790, 420616521711, 7007974415, 0, 0] := by
  rw [show A10K2.u4266 = KTree.node A10K2.u4262 (nat_lit 69002654) (nat_lit 15508892991) (nat_lit 0) A10K2.u4265 from rfl, totK_node, atot4262, atot4265]
  decide +kernel

theorem arows4274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4274 = true := by
  rw [show A10K2.u4274 = KTree.node A10K2.u4270 (nat_lit 69169920) (nat_lit 14676012242) (nat_lit 0) A10K2.u4273 from rfl, allE_node, arows4270, irow4274, arows4273]
  all_goals rfl

theorem atot4274 : totK PA10K2 A10K2.u4274 = [0, 1173992882942, 7128167359195, 14809589541725, 12546956763484, 3933259925762, 359696652400, 6318667960, 0, 0] := by
  rw [show A10K2.u4274 = KTree.node A10K2.u4270 (nat_lit 69169920) (nat_lit 14676012242) (nat_lit 0) A10K2.u4273 from rfl, totK_node, atot4270, atot4273]
  decide +kernel

theorem arows4281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4281 = true := by
  rw [show A10K2.u4281 = KTree.node A10K2.u4277 (nat_lit 69202839) (nat_lit 14313742118) (nat_lit 0) A10K2.u4280 from rfl, allE_node, arows4277, irow4281, arows4280]
  all_goals rfl

theorem atot4281 : totK PA10K2 A10K2.u4281 = [0, 869022221310, 4920131460635, 11574915646091, 13401002389422, 7077664922466, 1298046544518, 67457817768, 0, 0] := by
  rw [show A10K2.u4281 = KTree.node A10K2.u4277 (nat_lit 69202839) (nat_lit 14313742118) (nat_lit 0) A10K2.u4280 from rfl, totK_node, atot4277, atot4280]
  decide +kernel

theorem arows4291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4291 = true := by
  rw [show A10K2.u4291 = KTree.node A10K2.u4287 (nat_lit 69234096) (nat_lit 14358987854) (nat_lit 0) A10K2.u4290 from rfl, allE_node, arows4287, irow4291, arows4290]
  all_goals rfl

theorem atot4291 : totK PA10K2 A10K2.u4291 = [0, 1465870392664, 7962362463724, 14935624959300, 11082829789524, 2849977732415, 188951647449, 0, 0, 0] := by
  rw [show A10K2.u4291 = KTree.node A10K2.u4287 (nat_lit 69234096) (nat_lit 14358987854) (nat_lit 0) A10K2.u4290 from rfl, totK_node, atot4287, atot4290]
  decide +kernel

theorem arows4298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4298 = true := by
  rw [show A10K2.u4298 = KTree.node A10K2.u4294 (nat_lit 69264826) (nat_lit 13978669778) (nat_lit 0) A10K2.u4297 from rfl, allE_node, arows4294, irow4298, arows4297]
  all_goals rfl

theorem atot4298 : totK PA10K2 A10K2.u4298 = [0, 998092700503, 5693666131966, 12688582346781, 12762385997672, 5097842714739, 774264556170, 36196801203, 0, 0] := by
  rw [show A10K2.u4298 = KTree.node A10K2.u4294 (nat_lit 69264826) (nat_lit 13978669778) (nat_lit 0) A10K2.u4297 from rfl, totK_node, atot4294, atot4297]
  decide +kernel

theorem arows4306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4306 = true := by
  rw [show A10K2.u4306 = KTree.node A10K2.u4302 (nat_lit 69360404) (nat_lit 13252706185) (nat_lit 0) A10K2.u4305 from rfl, allE_node, arows4302, irow4306, arows4305]
  all_goals rfl

theorem atot4306 : totK PA10K2 A10K2.u4306 = [0, 1056485411382, 7325171551340, 15599415626108, 11403005221199, 2249949445946, 93690930761, 0, 0, 0] := by
  rw [show A10K2.u4306 = KTree.node A10K2.u4302 (nat_lit 69360404) (nat_lit 13252706185) (nat_lit 0) A10K2.u4305 from rfl, totK_node, atot4302, atot4305]
  decide +kernel

theorem arows4313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4313 = true := by
  rw [show A10K2.u4313 = KTree.node A10K2.u4309 (nat_lit 69413965) (nat_lit 4336150654) (nat_lit 0) A10K2.u4312 from rfl, allE_node, arows4309, irow4313, arows4312]
  all_goals rfl

theorem atot4313 : totK PA10K2 A10K2.u4313 = [0, 1887456069663, 8812554264724, 14884467294871, 10777751544351, 2944541853799, 249746556248, 5976421810, 0, 0] := by
  rw [show A10K2.u4313 = KTree.node A10K2.u4309 (nat_lit 69413965) (nat_lit 4336150654) (nat_lit 0) A10K2.u4312 from rfl, totK_node, atot4309, atot4312]
  decide +kernel

theorem arows4322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4322 = true := by
  rw [show A10K2.u4322 = KTree.node A10K2.u4318 (nat_lit 69461214) (nat_lit 11389925001) (nat_lit 0) A10K2.u4321 from rfl, allE_node, arows4318, irow4322, arows4321]
  all_goals rfl

theorem atot4322 : totK PA10K2 A10K2.u4322 = [0, 0, 2749662691644, 11645004129830, 16077579250947, 7836045694151, 1145458906789, 41475476640, 0, 0] := by
  rw [show A10K2.u4322 = KTree.node A10K2.u4318 (nat_lit 69461214) (nat_lit 11389925001) (nat_lit 0) A10K2.u4321 from rfl, totK_node, atot4318, atot4321]
  decide +kernel

theorem arows4329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4329 = true := by
  rw [show A10K2.u4329 = KTree.node A10K2.u4325 (nat_lit 69493004) (nat_lit 11654116419) (nat_lit 0) A10K2.u4328 from rfl, allE_node, arows4325, irow4329, arows4328]
  all_goals rfl

theorem atot4329 : totK PA10K2 A10K2.u4329 = [0, 0, 1462674615380, 8453228244614, 15812513109799, 10218504919182, 2006274725284, 102790279195, 0, 0] := by
  rw [show A10K2.u4329 = KTree.node A10K2.u4325 (nat_lit 69493004) (nat_lit 11654116419) (nat_lit 0) A10K2.u4328 from rfl, totK_node, atot4325, atot4328]
  decide +kernel

theorem arows4337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4337 = true := by
  rw [show A10K2.u4337 = KTree.node A10K2.u4333 (nat_lit 69525563) (nat_lit 4672887371) (nat_lit 0) A10K2.u4336 from rfl, allE_node, arows4333, irow4337, arows4336]
  all_goals rfl

theorem atot4337 : totK PA10K2 A10K2.u4337 = [0, 0, 792926426390, 5098185368950, 12344275541915, 12889285145833, 5468227293512, 838610121013, 36134558889, 0] := by
  rw [show A10K2.u4337 = KTree.node A10K2.u4333 (nat_lit 69525563) (nat_lit 4672887371) (nat_lit 0) A10K2.u4336 from rfl, totK_node, atot4333, atot4336]
  decide +kernel

theorem arows4344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4344 = true := by
  rw [show A10K2.u4344 = KTree.node A10K2.u4340 (nat_lit 69622114) (nat_lit 12517783050) (nat_lit 0) A10K2.u4343 from rfl, allE_node, arows4340, irow4344, arows4343]
  all_goals rfl

theorem atot4344 : totK PA10K2 A10K2.u4344 = [0, 0, 1256336767976, 7830425964860, 15631415211348, 10416849205345, 1967262186051, 107116236701, 0, 0] := by
  rw [show A10K2.u4344 = KTree.node A10K2.u4340 (nat_lit 69622114) (nat_lit 12517783050) (nat_lit 0) A10K2.u4343 from rfl, totK_node, atot4340, atot4343]
  decide +kernel

theorem arows4356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4356 = true := by
  rw [show A10K2.u4356 = KTree.node A10K2.u4352 (nat_lit 69676766) (nat_lit 11283310526) (nat_lit 0) A10K2.u4355 from rfl, allE_node, arows4352, irow4356, arows4355]
  all_goals rfl

theorem atot4356 : totK PA10K2 A10K2.u4356 = [0, 583356039855, 3817847104943, 10267415572076, 13806001149807, 8450061591987, 2180366739738, 227296609147, 5676195732, 0] := by
  rw [show A10K2.u4356 = KTree.node A10K2.u4352 (nat_lit 69676766) (nat_lit 11283310526) (nat_lit 0) A10K2.u4355 from rfl, totK_node, atot4352, atot4355]
  decide +kernel

theorem arows4363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4363 = true := by
  rw [show A10K2.u4363 = KTree.node A10K2.u4359 (nat_lit 70276247) (nat_lit 9324949875) (nat_lit 0) A10K2.u4362 from rfl, allE_node, arows4359, irow4363, arows4362]
  all_goals rfl

theorem atot4363 : totK PA10K2 A10K2.u4363 = [0, 1571194275863, 8645537823704, 15825072284802, 10338593551324, 2025935356824, 98356594220, 0, 0, 0] := by
  rw [show A10K2.u4363 = KTree.node A10K2.u4359 (nat_lit 70276247) (nat_lit 9324949875) (nat_lit 0) A10K2.u4362 from rfl, totK_node, atot4359, atot4362]
  decide +kernel

theorem arows4371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4371 = true := by
  rw [show A10K2.u4371 = KTree.node A10K2.u4367 (nat_lit 70309987) (nat_lit 5047557537) (nat_lit 0) A10K2.u4370 from rfl, allE_node, arows4367, irow4371, arows4370]
  all_goals rfl

theorem atot4371 : totK PA10K2 A10K2.u4371 = [0, 762984113060, 4927699164756, 12250614264457, 13643922146008, 5871054517043, 861671818416, 36196801203, 0, 0] := by
  rw [show A10K2.u4371 = KTree.node A10K2.u4367 (nat_lit 70309987) (nat_lit 5047557537) (nat_lit 0) A10K2.u4370 from rfl, totK_node, atot4367, atot4370]
  decide +kernel

theorem arows4378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4378 = true := by
  rw [show A10K2.u4378 = KTree.node A10K2.u4374 (nat_lit 70363930) (nat_lit 12802278115) (nat_lit 0) A10K2.u4377 from rfl, allE_node, arows4374, irow4378, arows4377]
  all_goals rfl

theorem atot4378 : totK PA10K2 A10K2.u4378 = [0, 1358576695645, 7438783353059, 14415747924150, 11583767359437, 3314223685089, 295226820526, 6121173289, 0, 0] := by
  rw [show A10K2.u4378 = KTree.node A10K2.u4374 (nat_lit 70363930) (nat_lit 12802278115) (nat_lit 0) A10K2.u4377 from rfl, totK_node, atot4374, atot4377]
  decide +kernel

theorem arows4387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4387 = true := by
  rw [show A10K2.u4387 = KTree.node A10K2.u4383 (nat_lit 70400769) (nat_lit 9386387117) (nat_lit 0) A10K2.u4386 from rfl, allE_node, arows4383, irow4387, arows4386]
  all_goals rfl

theorem atot4387 : totK PA10K2 A10K2.u4387 = [0, 1671892701588, 8904604323840, 15789513464566, 9906490849041, 1837537818250, 94153116215, 0, 0, 0] := by
  rw [show A10K2.u4387 = KTree.node A10K2.u4383 (nat_lit 70400769) (nat_lit 9386387117) (nat_lit 0) A10K2.u4386 from rfl, totK_node, atot4383, atot4386]
  decide +kernel

theorem arows4394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4394 = true := by
  rw [show A10K2.u4394 = KTree.node A10K2.u4390 (nat_lit 70441017) (nat_lit 5731775458) (nat_lit 0) A10K2.u4393 from rfl, allE_node, arows4390, irow4394, arows4393]
  all_goals rfl

theorem atot4394 : totK PA10K2 A10K2.u4394 = [0, 0, 2783695480579, 11781056282660, 15660364840957, 6653456959120, 976400859266, 37172849495, 0, 0] := by
  rw [show A10K2.u4394 = KTree.node A10K2.u4390 (nat_lit 70441017) (nat_lit 5731775458) (nat_lit 0) A10K2.u4393 from rfl, totK_node, atot4390, atot4393]
  decide +kernel

theorem arows4402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4402 = true := by
  rw [show A10K2.u4402 = KTree.node A10K2.u4398 (nat_lit 70591634) (nat_lit 15945489470) (nat_lit 0) A10K2.u4401 from rfl, allE_node, arows4398, irow4402, arows4401]
  all_goals rfl

theorem atot4402 : totK PA10K2 A10K2.u4402 = [0, 0, 2569657671056, 11588011323306, 16397781890560, 7109550994640, 766736232230, 13207830636, 0, 0] := by
  rw [show A10K2.u4402 = KTree.node A10K2.u4398 (nat_lit 70591634) (nat_lit 15945489470) (nat_lit 0) A10K2.u4401 from rfl, totK_node, atot4398, atot4401]
  decide +kernel

theorem arows4409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4409 = true := by
  rw [show A10K2.u4409 = KTree.node A10K2.u4405 (nat_lit 70659740) (nat_lit 9450845453) (nat_lit 0) A10K2.u4408 from rfl, allE_node, arows4405, irow4409, arows4408]
  all_goals rfl

theorem atot4409 : totK PA10K2 A10K2.u4409 = [0, 0, 2245900502057, 10581025672270, 15878273294753, 7783254639459, 1188870557539, 48818064363, 0, 0] := by
  rw [show A10K2.u4409 = KTree.node A10K2.u4405 (nat_lit 70659740) (nat_lit 9450845453) (nat_lit 0) A10K2.u4408 from rfl, totK_node, atot4405, atot4408]
  decide +kernel

theorem arows4419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4419 = true := by
  rw [show A10K2.u4419 = KTree.node A10K2.u4415 (nat_lit 70703392) (nat_lit 12608327091) (nat_lit 0) A10K2.u4418 from rfl, allE_node, arows4415, irow4419, arows4418]
  all_goals rfl

theorem atot4419 : totK PA10K2 A10K2.u4419 = [0, 1193773950094, 5040241474885, 9183457785871, 11076953947794, 8270930125391, 2543556394611, 261362977913, 5976421810, 0] := by
  rw [show A10K2.u4419 = KTree.node A10K2.u4415 (nat_lit 70703392) (nat_lit 12608327091) (nat_lit 0) A10K2.u4418 from rfl, totK_node, atot4415, atot4418]
  decide +kernel

theorem arows4426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4426 = true := by
  rw [show A10K2.u4426 = KTree.node A10K2.u4422 (nat_lit 70811015) (nat_lit 14707663872) (nat_lit 0) A10K2.u4425 from rfl, allE_node, arows4422, irow4426, arows4425]
  all_goals rfl

theorem atot4426 : totK PA10K2 A10K2.u4426 = [0, 1007843049981, 6321945023540, 13782586083777, 12589773962015, 4640505043306, 668449907764, 30650496230, 0, 0] := by
  rw [show A10K2.u4426 = KTree.node A10K2.u4422 (nat_lit 70811015) (nat_lit 14707663872) (nat_lit 0) A10K2.u4425 from rfl, totK_node, atot4422, atot4425]
  decide +kernel

theorem arows4434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4434 = true := by
  rw [show A10K2.u4434 = KTree.node A10K2.u4430 (nat_lit 70980038) (nat_lit 15443883701) (nat_lit 0) A10K2.u4433 from rfl, allE_node, arows4430, irow4434, arows4433]
  all_goals rfl

theorem atot4434 : totK PA10K2 A10K2.u4434 = [0, 1912539683153, 9313124454193, 15804445808763, 10474243571874, 2241515281726, 121303164474, 0, 0, 0] := by
  rw [show A10K2.u4434 = KTree.node A10K2.u4430 (nat_lit 70980038) (nat_lit 15443883701) (nat_lit 0) A10K2.u4433 from rfl, totK_node, atot4430, atot4433]
  decide +kernel

theorem arows4441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4441 = true := by
  rw [show A10K2.u4441 = KTree.node A10K2.u4437 (nat_lit 71012273) (nat_lit 9000570098) (nat_lit 0) A10K2.u4440 from rfl, allE_node, arows4437, irow4441, arows4440]
  all_goals rfl

theorem atot4441 : totK PA10K2 A10K2.u4441 = [0, 329574811601, 4133708940758, 13053600970971, 15267408959513, 6412784278367, 729441528006, 13671283666, 0, 0] := by
  rw [show A10K2.u4441 = KTree.node A10K2.u4437 (nat_lit 71012273) (nat_lit 9000570098) (nat_lit 0) A10K2.u4440 from rfl, totK_node, atot4437, atot4440]
  decide +kernel

theorem arows4450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4450 = true := by
  rw [show A10K2.u4450 = KTree.node A10K2.u4446 (nat_lit 71904699) (nat_lit 6967763597) (nat_lit 0) A10K2.u4449 from rfl, allE_node, arows4446, irow4450, arows4449]
  all_goals rfl

theorem atot4450 : totK PA10K2 A10K2.u4450 = [1600415090483, 7331351789763, 11075034579601, 7744621267671, 5895608882696, 4080408058538, 979338169383, 61110126106, 0, 0] := by
  rw [show A10K2.u4450 = KTree.node A10K2.u4446 (nat_lit 71904699) (nat_lit 6967763597) (nat_lit 0) A10K2.u4449 from rfl, totK_node, atot4446, atot4449]
  decide +kernel

theorem arows4457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4457 = true := by
  rw [show A10K2.u4457 = KTree.node A10K2.u4453 (nat_lit 71935929) (nat_lit 4856603406) (nat_lit 0) A10K2.u4456 from rfl, allE_node, arows4453, irow4457, arows4456]
  all_goals rfl

theorem atot4457 : totK PA10K2 A10K2.u4457 = [743410903023, 5182493293566, 13137427766023, 13624723467187, 5234027915217, 704364298826, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4457 = KTree.node A10K2.u4453 (nat_lit 71935929) (nat_lit 4856603406) (nat_lit 0) A10K2.u4456 from rfl, totK_node, atot4453, atot4456]
  decide +kernel

theorem arows4465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4465 = true := by
  rw [show A10K2.u4465 = KTree.node A10K2.u4461 (nat_lit 71964837) (nat_lit 7304506399) (nat_lit 0) A10K2.u4464 from rfl, allE_node, arows4461, irow4465, arows4464]
  all_goals rfl

theorem atot4465 : totK PA10K2 A10K2.u4465 = [1691825002314, 7900451699533, 13797778802370, 11008940317762, 3591643474385, 351169084654, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u4465 = KTree.node A10K2.u4461 (nat_lit 71964837) (nat_lit 7304506399) (nat_lit 0) A10K2.u4464 from rfl, totK_node, atot4461, atot4464]
  decide +kernel

theorem arows4472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4472 = true := by
  rw [show A10K2.u4472 = KTree.node A10K2.u4468 (nat_lit 72002218) (nat_lit 12801644120) (nat_lit 0) A10K2.u4471 from rfl, allE_node, arows4468, irow4472, arows4471]
  all_goals rfl

theorem atot4472 : totK PA10K2 A10K2.u4472 = [647106639010, 5708331380116, 14328471718672, 13090721471749, 3965464220841, 393727296452, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4472 = KTree.node A10K2.u4468 (nat_lit 72002218) (nat_lit 12801644120) (nat_lit 0) A10K2.u4471 from rfl, totK_node, atot4468, atot4471]
  decide +kernel

theorem arows4483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4483 = true := by
  rw [show A10K2.u4483 = KTree.node A10K2.u4479 (nat_lit 72051726) (nat_lit 14689662443) (nat_lit 0) A10K2.u4482 from rfl, allE_node, arows4479, irow4483, arows4482]
  all_goals rfl

theorem atot4483 : totK PA10K2 A10K2.u4483 = [1611752829918, 8343888367481, 15373536941954, 11505107080748, 3185928684584, 227371579081, 0, 0, 0, 0] := by
  rw [show A10K2.u4483 = KTree.node A10K2.u4479 (nat_lit 72051726) (nat_lit 14689662443) (nat_lit 0) A10K2.u4482 from rfl, totK_node, atot4479, atot4482]
  decide +kernel

theorem arows4490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4490 = true := by
  rw [show A10K2.u4490 = KTree.node A10K2.u4486 (nat_lit 72086871) (nat_lit 6245813083) (nat_lit 0) A10K2.u4489 from rfl, allE_node, arows4486, irow4490, arows4489]
  all_goals rfl

theorem atot4490 : totK PA10K2 A10K2.u4490 = [0, 1965741574770, 9704556596596, 15977006347459, 9729727905733, 1918168145784, 99925900411, 0, 0, 0] := by
  rw [show A10K2.u4490 = KTree.node A10K2.u4486 (nat_lit 72086871) (nat_lit 6245813083) (nat_lit 0) A10K2.u4489 from rfl, totK_node, atot4486, atot4489]
  decide +kernel

theorem arows4498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4498 = true := by
  rw [show A10K2.u4498 = KTree.node A10K2.u4494 (nat_lit 72183452) (nat_lit 9657341456) (nat_lit 0) A10K2.u4497 from rfl, allE_node, arows4494, irow4498, arows4497]
  all_goals rfl

theorem atot4498 : totK PA10K2 A10K2.u4498 = [0, 1469934413965, 7854638525329, 14627613666601, 10891083634418, 3226568943813, 445134726202, 25565504801, 0, 0] := by
  rw [show A10K2.u4498 = KTree.node A10K2.u4494 (nat_lit 72183452) (nat_lit 9657341456) (nat_lit 0) A10K2.u4497 from rfl, totK_node, atot4494, atot4497]
  decide +kernel

theorem arows4505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4505 = true := by
  rw [show A10K2.u4505 = KTree.node A10K2.u4501 (nat_lit 72215962) (nat_lit 14554951347) (nat_lit 0) A10K2.u4504 from rfl, allE_node, arows4501, irow4505, arows4504]
  all_goals rfl

theorem atot4505 : totK PA10K2 A10K2.u4505 = [0, 1268414326845, 6852625742512, 13624316811820, 11819567911550, 4103376942696, 478651807998, 11138589073, 0, 0] := by
  rw [show A10K2.u4505 = KTree.node A10K2.u4501 (nat_lit 72215962) (nat_lit 14554951347) (nat_lit 0) A10K2.u4504 from rfl, totK_node, atot4501, atot4504]
  decide +kernel

theorem arows4514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4514 = true := by
  rw [show A10K2.u4514 = KTree.node A10K2.u4510 (nat_lit 72254242) (nat_lit 9557168626) (nat_lit 0) A10K2.u4513 from rfl, allE_node, arows4510, irow4514, arows4513]
  all_goals rfl

theorem atot4514 : totK PA10K2 A10K2.u4514 = [0, 789970551885, 6187601902331, 14920068883732, 12655816373219, 2942066576673, 157714755763, 0, 0, 0] := by
  rw [show A10K2.u4514 = KTree.node A10K2.u4510 (nat_lit 72254242) (nat_lit 9557168626) (nat_lit 0) A10K2.u4513 from rfl, totK_node, atot4510, atot4513]
  decide +kernel

theorem arows4521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4521 = true := by
  rw [show A10K2.u4521 = KTree.node A10K2.u4517 (nat_lit 72300904) (nat_lit 7504201925) (nat_lit 0) A10K2.u4520 from rfl, allE_node, arows4517, irow4521, arows4520]
  all_goals rfl

theorem atot4521 : totK PA10K2 A10K2.u4521 = [301604122727, 2652352040149, 9240861489595, 14527144834451, 10025754020939, 2739682829525, 270417085052, 6239673734, 0, 0] := by
  rw [show A10K2.u4521 = KTree.node A10K2.u4517 (nat_lit 72300904) (nat_lit 7504201925) (nat_lit 0) A10K2.u4520 from rfl, totK_node, atot4517, atot4520]
  decide +kernel

theorem arows4529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4529 = true := by
  rw [show A10K2.u4529 = KTree.node A10K2.u4525 (nat_lit 72370973) (nat_lit 6299948848) (nat_lit 0) A10K2.u4528 from rfl, allE_node, arows4525, irow4529, arows4528]
  all_goals rfl

theorem atot4529 : totK PA10K2 A10K2.u4529 = [1237056671062, 7232584770330, 14130368058359, 11214007784225, 3991887121425, 618211488831, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4529 = KTree.node A10K2.u4525 (nat_lit 72370973) (nat_lit 6299948848) (nat_lit 0) A10K2.u4528 from rfl, totK_node, atot4525, atot4528]
  decide +kernel

theorem arows4536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4536 = true := by
  rw [show A10K2.u4536 = KTree.node A10K2.u4532 (nat_lit 72429463) (nat_lit 14522178997) (nat_lit 0) A10K2.u4535 from rfl, allE_node, arows4532, irow4536, arows4535]
  all_goals rfl

theorem atot4536 : totK PA10K2 A10K2.u4536 = [1606932462884, 8126511738799, 14594794528908, 10751495229559, 2931028645073, 262460939048, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4536 = KTree.node A10K2.u4532 (nat_lit 72429463) (nat_lit 14522178997) (nat_lit 0) A10K2.u4535 from rfl, totK_node, atot4532, atot4535]
  decide +kernel

theorem arows4546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4546 = true := by
  rw [show A10K2.u4546 = KTree.node A10K2.u4542 (nat_lit 72462234) (nat_lit 14591627111) (nat_lit 0) A10K2.u4545 from rfl, allE_node, arows4542, irow4546, arows4545]
  all_goals rfl

theorem atot4546 : totK PA10K2 A10K2.u4546 = [554803763168, 4241080991644, 11939522729147, 14370597617648, 6417302709484, 911677027475, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4546 = KTree.node A10K2.u4542 (nat_lit 72462234) (nat_lit 14591627111) (nat_lit 0) A10K2.u4545 from rfl, totK_node, atot4542, atot4545]
  decide +kernel

theorem arows4553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4553 = true := by
  rw [show A10K2.u4553 = KTree.node A10K2.u4549 (nat_lit 72492726) (nat_lit 14641145601) (nat_lit 0) A10K2.u4552 from rfl, allE_node, arows4549, irow4553, arows4552]
  all_goals rfl

theorem atot4553 : totK PA10K2 A10K2.u4553 = [2254573189466, 9911001042438, 15046342774341, 9203400890642, 2080175508407, 132368933516, 0, 0, 0, 0] := by
  rw [show A10K2.u4553 = KTree.node A10K2.u4549 (nat_lit 72492726) (nat_lit 14641145601) (nat_lit 0) A10K2.u4552 from rfl, totK_node, atot4549, atot4552]
  decide +kernel

theorem arows4561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4561 = true := by
  rw [show A10K2.u4561 = KTree.node A10K2.u4557 (nat_lit 72527530) (nat_lit 12668747883) (nat_lit 0) A10K2.u4560 from rfl, allE_node, arows4557, irow4561, arows4560]
  all_goals rfl

theorem atot4561 : totK PA10K2 A10K2.u4561 = [0, 3928543090894, 14103246639767, 14901610717621, 4653914445646, 432563266740, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4561 = KTree.node A10K2.u4557 (nat_lit 72527530) (nat_lit 12668747883) (nat_lit 0) A10K2.u4560 from rfl, totK_node, atot4557, atot4560]
  decide +kernel

theorem arows4568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4568 = true := by
  rw [show A10K2.u4568 = KTree.node A10K2.u4564 (nat_lit 72636706) (nat_lit 12646116095) (nat_lit 0) A10K2.u4567 from rfl, allE_node, arows4564, irow4568, arows4567]
  all_goals rfl

theorem atot4568 : totK PA10K2 A10K2.u4568 = [0, 2134089755599, 10000076167797, 15702887924612, 8914493177563, 1543583865379, 68625423345, 0, 0, 0] := by
  rw [show A10K2.u4568 = KTree.node A10K2.u4564 (nat_lit 72636706) (nat_lit 12646116095) (nat_lit 0) A10K2.u4567 from rfl, totK_node, atot4564, atot4567]
  decide +kernel

theorem arows4577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4577 = true := by
  rw [show A10K2.u4577 = KTree.node A10K2.u4573 (nat_lit 72744973) (nat_lit 5759762126) (nat_lit 0) A10K2.u4576 from rfl, allE_node, arows4573, irow4577, arows4576]
  all_goals rfl

theorem atot4577 : totK PA10K2 A10K2.u4577 = [0, 2340488480324, 10893312237577, 16158446783366, 8052863035701, 1162451980513, 43392108525, 0, 0, 0] := by
  rw [show A10K2.u4577 = KTree.node A10K2.u4573 (nat_lit 72744973) (nat_lit 5759762126) (nat_lit 0) A10K2.u4576 from rfl, totK_node, atot4573, atot4576]
  decide +kernel

theorem arows4584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4584 = true := by
  rw [show A10K2.u4584 = KTree.node A10K2.u4580 (nat_lit 72768298) (nat_lit 11406714635) (nat_lit 0) A10K2.u4583 from rfl, allE_node, arows4580, irow4584, arows4583]
  all_goals rfl

theorem atot4584 : totK PA10K2 A10K2.u4584 = [0, 836002267270, 6739805179359, 15561526125540, 11679948414746, 2484466102328, 150351458370, 0, 0, 0] := by
  rw [show A10K2.u4584 = KTree.node A10K2.u4580 (nat_lit 72768298) (nat_lit 11406714635) (nat_lit 0) A10K2.u4583 from rfl, totK_node, atot4580, atot4583]
  decide +kernel

theorem arows4592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4592 = true := by
  rw [show A10K2.u4592 = KTree.node A10K2.u4588 (nat_lit 72956755) (nat_lit 8866068140) (nat_lit 0) A10K2.u4591 from rfl, allE_node, arows4588, irow4592, arows4591]
  all_goals rfl

theorem atot4592 : totK PA10K2 A10K2.u4592 = [2211027775591, 9613443704272, 13637687088794, 7841867067153, 3665433476779, 1621304002283, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u4592 = KTree.node A10K2.u4588 (nat_lit 72956755) (nat_lit 8866068140) (nat_lit 0) A10K2.u4591 from rfl, totK_node, atot4588, atot4591]
  decide +kernel

theorem arows4599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4599 = true := by
  rw [show A10K2.u4599 = KTree.node A10K2.u4595 (nat_lit 72988960) (nat_lit 10038222892) (nat_lit 0) A10K2.u4598 from rfl, allE_node, arows4595, irow4599, arows4598]
  all_goals rfl

theorem atot4599 : totK PA10K2 A10K2.u4599 = [0, 2894010392051, 12188802598133, 16098913695737, 7054892277629, 946934909553, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4599 = KTree.node A10K2.u4595 (nat_lit 72988960) (nat_lit 10038222892) (nat_lit 0) A10K2.u4598 from rfl, totK_node, atot4595, atot4598]
  decide +kernel

theorem arows4612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4612 = true := by
  rw [show A10K2.u4612 = KTree.node A10K2.u4608 (nat_lit 73086345) (nat_lit 5456256781) (nat_lit 0) A10K2.u4611 from rfl, allE_node, arows4608, irow4612, arows4611]
  all_goals rfl

theorem atot4612 : totK PA10K2 A10K2.u4612 = [2245477168038, 10369551441551, 16143741184141, 9353213482588, 1830711291267, 108389447998, 0, 0, 0, 0] := by
  rw [show A10K2.u4612 = KTree.node A10K2.u4608 (nat_lit 73086345) (nat_lit 5456256781) (nat_lit 0) A10K2.u4611 from rfl, totK_node, atot4608, atot4611]
  decide +kernel

theorem arows4619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4619 = true := by
  rw [show A10K2.u4619 = KTree.node A10K2.u4615 (nat_lit 73117368) (nat_lit 10941187905) (nat_lit 0) A10K2.u4618 from rfl, allE_node, arows4615, irow4619, arows4618]
  all_goals rfl

theorem atot4619 : totK PA10K2 A10K2.u4619 = [0, 2363969785185, 10961255419880, 16592487385166, 8773649591080, 1235227418062, 26176060751, 0, 0, 0] := by
  rw [show A10K2.u4619 = KTree.node A10K2.u4615 (nat_lit 73117368) (nat_lit 10941187905) (nat_lit 0) A10K2.u4618 from rfl, totK_node, atot4615, atot4618]
  decide +kernel

theorem arows4627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4627 = true := by
  rw [show A10K2.u4627 = KTree.node A10K2.u4623 (nat_lit 73221531) (nat_lit 9866777688) (nat_lit 0) A10K2.u4626 from rfl, allE_node, arows4623, irow4627, arows4626]
  all_goals rfl

theorem atot4627 : totK PA10K2 A10K2.u4627 = [0, 2211027775591, 10214290419973, 15888324200925, 9222858953852, 1771107868639, 92712469127, 0, 0, 0] := by
  rw [show A10K2.u4627 = KTree.node A10K2.u4623 (nat_lit 73221531) (nat_lit 9866777688) (nat_lit 0) A10K2.u4626 from rfl, totK_node, atot4623, atot4626]
  decide +kernel

theorem arows4634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4634 = true := by
  rw [show A10K2.u4634 = KTree.node A10K2.u4630 (nat_lit 73255077) (nat_lit 7333572875) (nat_lit 0) A10K2.u4633 from rfl, allE_node, arows4630, irow4634, arows4633]
  all_goals rfl

theorem atot4634 : totK PA10K2 A10K2.u4634 = [0, 592737332747, 5238748942469, 14059110814542, 14302190991199, 4966230400271, 478934742878, 7151180950, 0, 0] := by
  rw [show A10K2.u4634 = KTree.node A10K2.u4630 (nat_lit 73255077) (nat_lit 7333572875) (nat_lit 0) A10K2.u4633 from rfl, totK_node, atot4630, atot4633]
  decide +kernel

theorem arows4643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4643 = true := by
  rw [show A10K2.u4643 = KTree.node A10K2.u4639 (nat_lit 73362483) (nat_lit 7031829568) (nat_lit 0) A10K2.u4642 from rfl, allE_node, arows4639, irow4643, arows4642]
  all_goals rfl

theorem atot4643 : totK PA10K2 A10K2.u4643 = [0, 1651245357751, 8346428125796, 15053733827864, 11372301568063, 3203377380188, 280115889625, 6318667960, 0, 0] := by
  rw [show A10K2.u4643 = KTree.node A10K2.u4639 (nat_lit 73362483) (nat_lit 7031829568) (nat_lit 0) A10K2.u4642 from rfl, totK_node, atot4639, atot4642]
  decide +kernel

theorem arows4650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4650 = true := by
  rw [show A10K2.u4650 = KTree.node A10K2.u4646 (nat_lit 73395358) (nat_lit 15266959024) (nat_lit 0) A10K2.u4649 from rfl, allE_node, arows4646, irow4650, arows4649]
  all_goals rfl

theorem atot4650 : totK PA10K2 A10K2.u4650 = [0, 871367436928, 4833904146188, 11327549280449, 13572174700975, 7401612087346, 1352256126300, 67457817768, 0, 0] := by
  rw [show A10K2.u4650 = KTree.node A10K2.u4646 (nat_lit 73395358) (nat_lit 15266959024) (nat_lit 0) A10K2.u4649 from rfl, totK_node, atot4646, atot4649]
  decide +kernel

theorem arows4658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4658 = true := by
  rw [show A10K2.u4658 = KTree.node A10K2.u4654 (nat_lit 74015111) (nat_lit 14471687564) (nat_lit 0) A10K2.u4657 from rfl, allE_node, arows4654, irow4658, arows4657]
  all_goals rfl

theorem atot4658 : totK PA10K2 A10K2.u4658 = [0, 1468752881077, 8285063713349, 15627491860359, 10769902747423, 2273407995003, 112142339492, 0, 0, 0] := by
  rw [show A10K2.u4658 = KTree.node A10K2.u4654 (nat_lit 74015111) (nat_lit 14471687564) (nat_lit 0) A10K2.u4657 from rfl, totK_node, atot4654, atot4657]
  decide +kernel

theorem arows4665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4665 = true := by
  rw [show A10K2.u4665 = KTree.node A10K2.u4661 (nat_lit 74045440) (nat_lit 11526800436) (nat_lit 0) A10K2.u4664 from rfl, allE_node, arows4661, irow4665, arows4664]
  all_goals rfl

theorem atot4665 : totK PA10K2 A10K2.u4665 = [0, 777954947991, 4784078085150, 11772154642356, 13566199100137, 6167146551168, 902282014535, 37204059898, 0, 0] := by
  rw [show A10K2.u4665 = KTree.node A10K2.u4661 (nat_lit 74045440) (nat_lit 11526800436) (nat_lit 0) A10K2.u4664 from rfl, totK_node, atot4661, atot4664]
  decide +kernel

theorem arows4675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4675 = true := by
  rw [show A10K2.u4675 = KTree.node A10K2.u4671 (nat_lit 74074630) (nat_lit 7651620720) (nat_lit 0) A10K2.u4674 from rfl, allE_node, arows4671, irow4675, arows4674]
  all_goals rfl

theorem atot4675 : totK PA10K2 A10K2.u4675 = [0, 1278612021435, 7963864593145, 15797644272608, 10949737496049, 2160659002948, 89208104994, 0, 0, 0] := by
  rw [show A10K2.u4675 = KTree.node A10K2.u4671 (nat_lit 74074630) (nat_lit 7651620720) (nat_lit 0) A10K2.u4674 from rfl, totK_node, atot4671, atot4674]
  decide +kernel

theorem arows4682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4682 = true := by
  rw [show A10K2.u4682 = KTree.node A10K2.u4678 (nat_lit 74131781) (nat_lit 6784448095) (nat_lit 0) A10K2.u4681 from rfl, allE_node, arows4678, irow4682, arows4681]
  all_goals rfl

theorem atot4682 : totK PA10K2 A10K2.u4682 = [0, 1891363057166, 8811701946565, 14805270600266, 10625774168250, 2841795189260, 277298185032, 6354482628, 0, 0] := by
  rw [show A10K2.u4682 = KTree.node A10K2.u4678 (nat_lit 74131781) (nat_lit 6784448095) (nat_lit 0) A10K2.u4681 from rfl, totK_node, atot4678, atot4681]
  decide +kernel

theorem arows4690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4690 = true := by
  rw [show A10K2.u4690 = KTree.node A10K2.u4686 (nat_lit 74167486) (nat_lit 15397379809) (nat_lit 0) A10K2.u4689 from rfl, allE_node, arows4686, irow4690, arows4689]
  all_goals rfl

theorem atot4690 : totK PA10K2 A10K2.u4690 = [0, 0, 2495293674052, 11216276764616, 16433072561735, 8577089274826, 1211008507480, 19026474010, 0, 0] := by
  rw [show A10K2.u4690 = KTree.node A10K2.u4686 (nat_lit 74167486) (nat_lit 15397379809) (nat_lit 0) A10K2.u4689 from rfl, totK_node, atot4686, atot4689]
  decide +kernel

theorem arows4697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4697 = true := by
  rw [show A10K2.u4697 = KTree.node A10K2.u4693 (nat_lit 74270491) (nat_lit 9971016880) (nat_lit 0) A10K2.u4696 from rfl, allE_node, arows4693, irow4697, arows4696]
  all_goals rfl

theorem atot4697 : totK PA10K2 A10K2.u4697 = [0, 0, 2332044230920, 10669241669420, 15860998702083, 8190373177113, 1354548876347, 74122011406, 0, 0] := by
  rw [show A10K2.u4697 = KTree.node A10K2.u4693 (nat_lit 74270491) (nat_lit 9971016880) (nat_lit 0) A10K2.u4696 from rfl, totK_node, atot4693, atot4696]
  decide +kernel

theorem arows4706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4706 = true := by
  rw [show A10K2.u4706 = KTree.node A10K2.u4702 (nat_lit 74302938) (nat_lit 14647958835) (nat_lit 0) A10K2.u4705 from rfl, allE_node, arows4702, irow4706, arows4705]
  all_goals rfl

theorem atot4706 : totK PA10K2 A10K2.u4706 = [0, 0, 468537272203, 4220824466976, 12187309023118, 13962299695243, 5941629356827, 888575063418, 36704093874, 0] := by
  rw [show A10K2.u4706 = KTree.node A10K2.u4702 (nat_lit 74302938) (nat_lit 14647958835) (nat_lit 0) A10K2.u4705 from rfl, totK_node, atot4702, atot4705]
  decide +kernel

theorem arows4713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4713 = true := by
  rw [show A10K2.u4713 = KTree.node A10K2.u4709 (nat_lit 74335418) (nat_lit 14662722679) (nat_lit 0) A10K2.u4712 from rfl, allE_node, arows4709, irow4713, arows4712]
  all_goals rfl

theorem atot4713 : totK PA10K2 A10K2.u4713 = [0, 0, 1583965336280, 8719778029686, 15815241407676, 9816082548065, 1713298631334, 75822853530, 0, 0] := by
  rw [show A10K2.u4713 = KTree.node A10K2.u4709 (nat_lit 74335418) (nat_lit 14662722679) (nat_lit 0) A10K2.u4712 from rfl, totK_node, atot4709, atot4712]
  decide +kernel

theorem arows4721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4721 = true := by
  rw [show A10K2.u4721 = KTree.node A10K2.u4717 (nat_lit 74393500) (nat_lit 8775296757) (nat_lit 0) A10K2.u4720 from rfl, allE_node, arows4717, irow4721, arows4720]
  all_goals rfl

theorem atot4721 : totK PA10K2 A10K2.u4721 = [0, 0, 1887337181482, 8965371932394, 14997705449941, 10299438037554, 2677182224003, 264003032990, 5982052406, 0] := by
  rw [show A10K2.u4721 = KTree.node A10K2.u4717 (nat_lit 74393500) (nat_lit 8775296757) (nat_lit 0) A10K2.u4720 from rfl, totK_node, atot4717, atot4720]
  decide +kernel

theorem arows4728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4728 = true := by
  rw [show A10K2.u4728 = KTree.node A10K2.u4724 (nat_lit 74465352) (nat_lit 13794873941) (nat_lit 0) A10K2.u4727 from rfl, allE_node, arows4724, irow4728, arows4727]
  all_goals rfl

theorem atot4728 : totK PA10K2 A10K2.u4728 = [0, 1538660793789, 7927209479923, 14199510509224, 10663735474772, 3823501712086, 690124808890, 41590655314, 0, 0] := by
  rw [show A10K2.u4728 = KTree.node A10K2.u4724 (nat_lit 74465352) (nat_lit 13794873941) (nat_lit 0) A10K2.u4727 from rfl, totK_node, atot4724, atot4727]
  decide +kernel

theorem arows4739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4739 = true := by
  rw [show A10K2.u4739 = KTree.node A10K2.u4735 (nat_lit 74526614) (nat_lit 15959983175) (nat_lit 0) A10K2.u4738 from rfl, allE_node, arows4735, irow4739, arows4738]
  all_goals rfl

theorem atot4739 : totK PA10K2 A10K2.u4739 = [0, 1606932462884, 8192642911942, 14723441332289, 10635194255631, 2746132416367, 254826065740, 5546304973, 0, 0] := by
  rw [show A10K2.u4739 = KTree.node A10K2.u4735 (nat_lit 74526614) (nat_lit 15959983175) (nat_lit 0) A10K2.u4738 from rfl, totK_node, atot4735, atot4738]
  decide +kernel

theorem arows4746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4746 = true := by
  rw [show A10K2.u4746 = KTree.node A10K2.u4742 (nat_lit 74559388) (nat_lit 7995690229) (nat_lit 0) A10K2.u4745 from rfl, allE_node, arows4742, irow4746, arows4745]
  all_goals rfl

theorem atot4746 : totK PA10K2 A10K2.u4746 = [0, 554803763168, 4270206593656, 11993910223334, 14349467324176, 6305306962339, 898389618009, 37204059898, 0, 0] := by
  rw [show A10K2.u4746 = KTree.node A10K2.u4742 (nat_lit 74559388) (nat_lit 7995690229) (nat_lit 0) A10K2.u4745 from rfl, totK_node, atot4742, atot4745]
  decide +kernel

theorem arows4754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4754 = true := by
  rw [show A10K2.u4754 = KTree.node A10K2.u4750 (nat_lit 74589925) (nat_lit 6622306198) (nat_lit 0) A10K2.u4753 from rfl, allE_node, arows4750, irow4754, arows4753]
  all_goals rfl

theorem atot4754 : totK PA10K2 A10K2.u4754 = [0, 2254573189466, 9962486322343, 15108229099472, 9108688357128, 2005475731266, 123791304298, 0, 0, 0] := by
  rw [show A10K2.u4754 = KTree.node A10K2.u4750 (nat_lit 74589925) (nat_lit 6622306198) (nat_lit 0) A10K2.u4753 from rfl, totK_node, atot4750, atot4753]
  decide +kernel

theorem arows4761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4761 = true := by
  rw [show A10K2.u4761 = KTree.node A10K2.u4757 (nat_lit 74624947) (nat_lit 9061299416) (nat_lit 0) A10K2.u4760 from rfl, allE_node, arows4757, irow4761, arows4760]
  all_goals rfl

theorem atot4761 : totK PA10K2 A10K2.u4761 = [0, 0, 3971147927840, 14231157762834, 14821229886775, 4450029021172, 424960279743, 6354482628, 0, 0] := by
  rw [show A10K2.u4761 = KTree.node A10K2.u4757 (nat_lit 74624947) (nat_lit 9061299416) (nat_lit 0) A10K2.u4760 from rfl, totK_node, atot4757, atot4760]
  decide +kernel

theorem arows4770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4770 = true := by
  rw [show A10K2.u4770 = KTree.node A10K2.u4766 (nat_lit 74786199) (nat_lit 14237883125) (nat_lit 0) A10K2.u4769 from rfl, allE_node, arows4766, irow4770, arows4769]
  all_goals rfl

theorem atot4770 : totK PA10K2 A10K2.u4770 = [0, 0, 2273404849331, 10648989269804, 16120298141342, 7893044226853, 1108525196636, 43254242352, 0, 0] := by
  rw [show A10K2.u4770 = KTree.node A10K2.u4766 (nat_lit 74786199) (nat_lit 14237883125) (nat_lit 0) A10K2.u4769 from rfl, totK_node, atot4766, atot4769]
  decide +kernel

theorem arows4777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4777 = true := by
  rw [show A10K2.u4777 = KTree.node A10K2.u4773 (nat_lit 74844257) (nat_lit 9952831216) (nat_lit 0) A10K2.u4776 from rfl, allE_node, arows4773, irow4777, arows4776]
  all_goals rfl

theorem atot4777 : totK PA10K2 A10K2.u4777 = [0, 0, 2080964769259, 10374532426220, 16476017066352, 8268600937504, 1149937101752, 43746946997, 0, 0] := by
  rw [show A10K2.u4777 = KTree.node A10K2.u4773 (nat_lit 74844257) (nat_lit 9952831216) (nat_lit 0) A10K2.u4776 from rfl, totK_node, atot4773, atot4776]
  decide +kernel

theorem arows4785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4785 = true := by
  rw [show A10K2.u4785 = KTree.node A10K2.u4781 (nat_lit 74877709) (nat_lit 5817459816) (nat_lit 0) A10K2.u4784 from rfl, allE_node, arows4781, irow4785, arows4784]
  all_goals rfl

theorem atot4785 : totK PA10K2 A10K2.u4785 = [0, 0, 836002267270, 6264565472697, 14659595989326, 11926408263816, 3126339616190, 221348492536, 0, 0] := by
  rw [show A10K2.u4785 = KTree.node A10K2.u4781 (nat_lit 74877709) (nat_lit 5817459816) (nat_lit 0) A10K2.u4784 from rfl, totK_node, atot4781, atot4784]
  decide +kernel

theorem arows4792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4792 = true := by
  rw [show A10K2.u4792 = KTree.node A10K2.u4788 (nat_lit 75057435) (nat_lit 9901724394) (nat_lit 0) A10K2.u4791 from rfl, allE_node, arows4788, irow4792, arows4791]
  all_goals rfl

theorem atot4792 : totK PA10K2 A10K2.u4792 = [0, 2207301526707, 10287407913923, 16022405038563, 9093507884578, 1530930582359, 168686915565, 86874954689, 6354482628, 0] := by
  rw [show A10K2.u4792 = KTree.node A10K2.u4788 (nat_lit 75057435) (nat_lit 9901724394) (nat_lit 0) A10K2.u4791 from rfl, totK_node, atot4788, atot4791]
  decide +kernel

theorem arows4802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4802 = true := by
  rw [show A10K2.u4802 = KTree.node A10K2.u4798 (nat_lit 75090082) (nat_lit 13912359954) (nat_lit 0) A10K2.u4801 from rfl, allE_node, arows4798, irow4802, arows4801]
  all_goals rfl

theorem atot4802 : totK PA10K2 A10K2.u4802 = [0, 592431485893, 4380660217794, 12105401815347, 14436792411409, 6568771577421, 955271197439, 36968589557, 0, 0] := by
  rw [show A10K2.u4802 = KTree.node A10K2.u4798 (nat_lit 75090082) (nat_lit 13912359954) (nat_lit 0) A10K2.u4801 from rfl, totK_node, atot4798, atot4801]
  decide +kernel

theorem arows4809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4809 = true := by
  rw [show A10K2.u4809 = KTree.node A10K2.u4805 (nat_lit 75194814) (nat_lit 16287430150) (nat_lit 0) A10K2.u4808 from rfl, allE_node, arows4805, irow4809, arows4808]
  all_goals rfl

theorem atot4809 : totK PA10K2 A10K2.u4809 = [0, 1651306797485, 8777720762275, 15923500356094, 10980001676255, 2430706006856, 119406956821, 0, 0, 0] := by
  rw [show A10K2.u4809 = KTree.node A10K2.u4805 (nat_lit 75194814) (nat_lit 16287430150) (nat_lit 0) A10K2.u4808 from rfl, totK_node, atot4805, atot4808]
  decide +kernel

theorem arows4817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4817 = true := by
  rw [show A10K2.u4817 = KTree.node A10K2.u4813 (nat_lit 75227214) (nat_lit 10904956324) (nat_lit 0) A10K2.u4816 from rfl, allE_node, arows4813, irow4817, arows4816]
  all_goals rfl

theorem atot4817 : totK PA10K2 A10K2.u4817 = [374610277362, 1242783310141, 3039928831847, 9285154252418, 14956687946177, 9071595335095, 1632695547828, 74789331576, 0, 0] := by
  rw [show A10K2.u4817 = KTree.node A10K2.u4813 (nat_lit 75227214) (nat_lit 10904956324) (nat_lit 0) A10K2.u4816 from rfl, totK_node, atot4813, atot4816]
  decide +kernel

theorem arows4824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4824 = true := by
  rw [show A10K2.u4824 = KTree.node A10K2.u4820 (nat_lit 75516773) (nat_lit 7253494417) (nat_lit 0) A10K2.u4823 from rfl, allE_node, arows4820, irow4824, arows4823]
  all_goals rfl

theorem atot4824 : totK PA10K2 A10K2.u4824 = [1835885123726, 9383304138755, 15792986768333, 9689562999785, 1857669445520, 86741410326, 0, 0, 0, 0] := by
  rw [show A10K2.u4824 = KTree.node A10K2.u4820 (nat_lit 75516773) (nat_lit 7253494417) (nat_lit 0) A10K2.u4823 from rfl, totK_node, atot4820, atot4823]
  decide +kernel

theorem arows4833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4833 = true := by
  rw [show A10K2.u4833 = KTree.node A10K2.u4829 (nat_lit 75549459) (nat_lit 9867549172) (nat_lit 0) A10K2.u4832 from rfl, allE_node, arows4829, irow4833, arows4832]
  all_goals rfl

theorem atot4833 : totK PA10K2 A10K2.u4833 = [778776062315, 4886479373390, 12045942458709, 13632197101816, 5960515014437, 875738259589, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u4833 = KTree.node A10K2.u4829 (nat_lit 75549459) (nat_lit 9867549172) (nat_lit 0) A10K2.u4832 from rfl, totK_node, atot4829, atot4832]
  decide +kernel

theorem arows4840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4840 = true := by
  rw [show A10K2.u4840 = KTree.node A10K2.u4836 (nat_lit 75646142) (nat_lit 9968306719) (nat_lit 0) A10K2.u4839 from rfl, allE_node, arows4836, irow4840, arows4839]
  all_goals rfl

theorem atot4840 : totK PA10K2 A10K2.u4840 = [1378691090337, 8063804158742, 15590779685047, 10854492481398, 2242206576356, 107738090636, 0, 0, 0, 0] := by
  rw [show A10K2.u4840 = KTree.node A10K2.u4836 (nat_lit 75646142) (nat_lit 9968306719) (nat_lit 0) A10K2.u4839 from rfl, totK_node, atot4836, atot4839]
  decide +kernel

theorem arows4848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4848 = true := by
  rw [show A10K2.u4848 = KTree.node A10K2.u4844 (nat_lit 75694933) (nat_lit 6001099445) (nat_lit 0) A10K2.u4847 from rfl, allE_node, arows4844, irow4848, arows4847]
  all_goals rfl

theorem atot4848 : totK PA10K2 A10K2.u4848 = [1364381863375, 7149231153629, 14105022178527, 12020292488161, 3683803224911, 386175819749, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4848 = KTree.node A10K2.u4844 (nat_lit 75694933) (nat_lit 6001099445) (nat_lit 0) A10K2.u4847 from rfl, totK_node, atot4844, atot4847]
  decide +kernel

theorem arows4855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4855 = true := by
  rw [show A10K2.u4855 = KTree.node A10K2.u4851 (nat_lit 75754683) (nat_lit 7104203533) (nat_lit 0) A10K2.u4854 from rfl, allE_node, arows4851, irow4855, arows4854]
  all_goals rfl

theorem atot4855 : totK PA10K2 A10K2.u4855 = [0, 2513237670223, 10920839711744, 15816671240516, 8470228271408, 1568993845841, 87229086806, 0, 0, 0] := by
  rw [show A10K2.u4855 = KTree.node A10K2.u4851 (nat_lit 75754683) (nat_lit 7104203533) (nat_lit 0) A10K2.u4854 from rfl, totK_node, atot4851, atot4854]
  decide +kernel

theorem arows4867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4867 = true := by
  rw [show A10K2.u4867 = KTree.node A10K2.u4863 (nat_lit 75787277) (nat_lit 5166133133) (nat_lit 0) A10K2.u4866 from rfl, allE_node, arows4863, irow4867, arows4866]
  all_goals rfl

theorem atot4867 : totK PA10K2 A10K2.u4867 = [0, 1371482565093, 7722888708694, 14717859683685, 10879499114618, 3124236040350, 435771274855, 25239774317, 0, 0] := by
  rw [show A10K2.u4867 = KTree.node A10K2.u4863 (nat_lit 75787277) (nat_lit 5166133133) (nat_lit 0) A10K2.u4866 from rfl, totK_node, atot4863, atot4866]
  decide +kernel

theorem arows4874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4874 = true := by
  rw [show A10K2.u4874 = KTree.node A10K2.u4870 (nat_lit 75820510) (nat_lit 15120347421) (nat_lit 0) A10K2.u4873 from rfl, allE_node, arows4870, irow4874, arows4873]
  all_goals rfl

theorem atot4874 : totK PA10K2 A10K2.u4874 = [0, 1336795214440, 6633211562950, 13180470335934, 12077923530067, 4230899636747, 488559142357, 10894784572, 0, 0] := by
  rw [show A10K2.u4874 = KTree.node A10K2.u4870 (nat_lit 75820510) (nat_lit 15120347421) (nat_lit 0) A10K2.u4873 from rfl, totK_node, atot4870, atot4873]
  decide +kernel

theorem arows4882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4882 = true := by
  rw [show A10K2.u4882 = KTree.node A10K2.u4878 (nat_lit 75923733) (nat_lit 6796925496) (nat_lit 0) A10K2.u4881 from rfl, allE_node, arows4878, irow4882, arows4881]
  all_goals rfl

theorem atot4882 : totK PA10K2 A10K2.u4882 = [0, 819545818442, 6856756619927, 15696029712514, 11720031628532, 2444514698109, 119945278399, 0, 0, 0] := by
  rw [show A10K2.u4882 = KTree.node A10K2.u4878 (nat_lit 75923733) (nat_lit 6796925496) (nat_lit 0) A10K2.u4881 from rfl, totK_node, atot4878, atot4881]
  decide +kernel

theorem arows4889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4889 = true := by
  rw [show A10K2.u4889 = KTree.node A10K2.u4885 (nat_lit 75984054) (nat_lit 16606316129) (nat_lit 0) A10K2.u4888 from rfl, allE_node, arows4885, irow4889, arows4888]
  all_goals rfl

theorem atot4889 : totK PA10K2 A10K2.u4889 = [848323660542, 4787084145920, 10765421624153, 12568115321078, 7730553387487, 2244528411022, 241466383606, 5676195732, 0, 0] := by
  rw [show A10K2.u4889 = KTree.node A10K2.u4885 (nat_lit 75984054) (nat_lit 16606316129) (nat_lit 0) A10K2.u4888 from rfl, totK_node, atot4885, atot4888]
  decide +kernel

theorem arows4898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4898 = true := by
  rw [show A10K2.u4898 = KTree.node A10K2.u4894 (nat_lit 76113645) (nat_lit 5357365132) (nat_lit 0) A10K2.u4897 from rfl, allE_node, arows4894, irow4898, arows4897]
  all_goals rfl

theorem atot4898 : totK PA10K2 A10K2.u4898 = [1376555752418, 7778177647202, 15201038058901, 11474196648543, 2874229455960, 168589071346, 0, 0, 0, 0] := by
  rw [show A10K2.u4898 = KTree.node A10K2.u4894 (nat_lit 76113645) (nat_lit 5357365132) (nat_lit 0) A10K2.u4897 from rfl, totK_node, atot4894, atot4897]
  decide +kernel

theorem arows4905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4905 = true := by
  rw [show A10K2.u4905 = KTree.node A10K2.u4901 (nat_lit 76146334) (nat_lit 14483565660) (nat_lit 0) A10K2.u4904 from rfl, allE_node, arows4901, irow4905, arows4904]
  all_goals rfl

theorem atot4905 : totK PA10K2 A10K2.u4905 = [1141181548011, 5950744101529, 12241899767462, 12421642106876, 5519397775293, 855134737193, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4905 = KTree.node A10K2.u4901 (nat_lit 76146334) (nat_lit 14483565660) (nat_lit 0) A10K2.u4904 from rfl, totK_node, atot4901, atot4904]
  decide +kernel

theorem arows4913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4913 = true := by
  rw [show A10K2.u4913 = KTree.node A10K2.u4909 (nat_lit 76174620) (nat_lit 12116249641) (nat_lit 0) A10K2.u4912 from rfl, allE_node, arows4909, irow4913, arows4912]
  all_goals rfl

theorem atot4913 : totK PA10K2 A10K2.u4913 = [1017553662282, 7193049492111, 15549421056129, 11819895549585, 2605989092570, 134189215387, 0, 0, 0, 0] := by
  rw [show A10K2.u4913 = KTree.node A10K2.u4909 (nat_lit 76174620) (nat_lit 12116249641) (nat_lit 0) A10K2.u4912 from rfl, totK_node, atot4909, atot4912]
  decide +kernel

theorem arows4920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4920 = true := by
  rw [show A10K2.u4920 = KTree.node A10K2.u4916 (nat_lit 76232410) (nat_lit 13971053593) (nat_lit 0) A10K2.u4919 from rfl, allE_node, arows4916, irow4920, arows4919]
  all_goals rfl

theorem atot4920 : totK PA10K2 A10K2.u4920 = [1369613956845, 7217077574026, 14331758415357, 12262320780264, 3869982428799, 405102820294, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4920 = KTree.node A10K2.u4916 (nat_lit 76232410) (nat_lit 13971053593) (nat_lit 0) A10K2.u4919 from rfl, totK_node, atot4916, atot4919]
  decide +kernel

theorem arows4930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4930 = true := by
  rw [show A10K2.u4930 = KTree.node A10K2.u4926 (nat_lit 76283606) (nat_lit 15056077634) (nat_lit 0) A10K2.u4929 from rfl, allE_node, arows4926, irow4930, arows4929]
  all_goals rfl

theorem atot4930 : totK PA10K2 A10K2.u4930 = [0, 2240332991468, 10292509144222, 15731438511154, 9124931260611, 1763940456724, 93858941933, 0, 0, 0] := by
  rw [show A10K2.u4930 = KTree.node A10K2.u4926 (nat_lit 76283606) (nat_lit 15056077634) (nat_lit 0) A10K2.u4929 from rfl, totK_node, atot4926, atot4929]
  decide +kernel

theorem arows4937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4937 = true := by
  rw [show A10K2.u4937 = KTree.node A10K2.u4933 (nat_lit 76381640) (nat_lit 10799553120) (nat_lit 0) A10K2.u4936 from rfl, allE_node, arows4933, irow4937, arows4936]
  all_goals rfl

theorem atot4937 : totK PA10K2 A10K2.u4937 = [0, 912923523059, 6259880659697, 14005130349198, 12241807399903, 4340987016851, 640316662214, 31018567651, 0, 0] := by
  rw [show A10K2.u4937 = KTree.node A10K2.u4933 (nat_lit 76381640) (nat_lit 10799553120) (nat_lit 0) A10K2.u4936 from rfl, totK_node, atot4933, atot4936]
  decide +kernel

theorem arows4945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4945 = true := by
  rw [show A10K2.u4945 = KTree.node A10K2.u4941 (nat_lit 76417856) (nat_lit 13576200573) (nat_lit 0) A10K2.u4944 from rfl, allE_node, arows4941, irow4945, arows4944]
  all_goals rfl

theorem atot4945 : totK PA10K2 A10K2.u4945 = [0, 1574795350709, 7676659146239, 14064099552383, 11264584288266, 3382008178038, 315238620839, 5685526223, 0, 0] := by
  rw [show A10K2.u4945 = KTree.node A10K2.u4941 (nat_lit 76417856) (nat_lit 13576200573) (nat_lit 0) A10K2.u4944 from rfl, totK_node, atot4941, atot4944]
  decide +kernel

theorem arows4952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4952 = true := by
  rw [show A10K2.u4952 = KTree.node A10K2.u4948 (nat_lit 76457708) (nat_lit 11121599702) (nat_lit 0) A10K2.u4951 from rfl, allE_node, arows4948, irow4952, arows4951]
  all_goals rfl

theorem atot4952 : totK PA10K2 A10K2.u4952 = [0, 888956116483, 6212301433274, 14355974428667, 12506544162835, 3402814706242, 302695564235, 6239673734, 0, 0] := by
  rw [show A10K2.u4952 = KTree.node A10K2.u4948 (nat_lit 76457708) (nat_lit 11121599702) (nat_lit 0) A10K2.u4951 from rfl, totK_node, atot4948, atot4951]
  decide +kernel

theorem arows4961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4961 = true := by
  rw [show A10K2.u4961 = KTree.node A10K2.u4957 (nat_lit 76510686) (nat_lit 15040179094) (nat_lit 0) A10K2.u4960 from rfl, allE_node, arows4957, irow4961, arows4960]
  all_goals rfl

theorem atot4961 : totK PA10K2 A10K2.u4961 = [912565010242, 5015898909387, 11448528507691, 13129962316616, 7145338930992, 1508728954229, 87386032561, 0, 0, 0] := by
  rw [show A10K2.u4961 = KTree.node A10K2.u4957 (nat_lit 76510686) (nat_lit 15040179094) (nat_lit 0) A10K2.u4960 from rfl, totK_node, atot4957, atot4960]
  decide +kernel

theorem arows4968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4968 = true := by
  rw [show A10K2.u4968 = KTree.node A10K2.u4964 (nat_lit 76575624) (nat_lit 14170549419) (nat_lit 0) A10K2.u4967 from rfl, allE_node, arows4964, irow4968, arows4967]
  all_goals rfl

theorem atot4968 : totK PA10K2 A10K2.u4968 = [1132860514623, 6649047407295, 13581144549920, 11794943248620, 4376791410233, 657208342064, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4968 = KTree.node A10K2.u4964 (nat_lit 76575624) (nat_lit 14170549419) (nat_lit 0) A10K2.u4967 from rfl, totK_node, atot4964, atot4967]
  decide +kernel

theorem arows4976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4976 = true := by
  rw [show A10K2.u4976 = KTree.node A10K2.u4972 (nat_lit 76622996) (nat_lit 10750349994) (nat_lit 0) A10K2.u4975 from rfl, allE_node, arows4972, irow4976, arows4975]
  all_goals rfl

theorem atot4976 : totK PA10K2 A10K2.u4976 = [1590835445191, 8057072631713, 14443006455069, 10870159133441, 3110121132500, 295259876685, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4976 = KTree.node A10K2.u4972 (nat_lit 76622996) (nat_lit 10750349994) (nat_lit 0) A10K2.u4975 from rfl, totK_node, atot4972, atot4975]
  decide +kernel

theorem arows4983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4983 = true := by
  rw [show A10K2.u4983 = KTree.node A10K2.u4979 (nat_lit 76656588) (nat_lit 11933677) (nat_lit 0) A10K2.u4982 from rfl, allE_node, arows4979, irow4983, arows4982]
  all_goals rfl

theorem atot4983 : totK PA10K2 A10K2.u4983 = [461607179050, 4087596054541, 12104818818201, 14371333619321, 6293973915732, 905173571002, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4983 = KTree.node A10K2.u4979 (nat_lit 76656588) (nat_lit 11933677) (nat_lit 0) A10K2.u4982 from rfl, totK_node, atot4979, atot4982]
  decide +kernel

theorem arows4994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4994 = true := by
  rw [show A10K2.u4994 = KTree.node A10K2.u4990 (nat_lit 76686775) (nat_lit 12677354102) (nat_lit 0) A10K2.u4993 from rfl, allE_node, arows4990, irow4994, arows4993]
  all_goals rfl

theorem atot4994 : totK PA10K2 A10K2.u4994 = [2343832716771, 9950906229251, 14976640685528, 9053987888671, 1981632899300, 126809299706, 0, 0, 0, 0] := by
  rw [show A10K2.u4994 = KTree.node A10K2.u4990 (nat_lit 76686775) (nat_lit 12677354102) (nat_lit 0) A10K2.u4993 from rfl, totK_node, atot4990, atot4993]
  decide +kernel

theorem arows5001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5001 = true := by
  rw [show A10K2.u5001 = KTree.node A10K2.u4997 (nat_lit 76720940) (nat_lit 13411360507) (nat_lit 0) A10K2.u5000 from rfl, allE_node, arows4997, irow5001, arows5000]
  all_goals rfl

theorem atot5001 : totK PA10K2 A10K2.u5001 = [0, 4130288379624, 14227635766904, 14678181132056, 4521384424592, 426208662832, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5001 = KTree.node A10K2.u4997 (nat_lit 76720940) (nat_lit 13411360507) (nat_lit 0) A10K2.u5000 from rfl, totK_node, atot4997, atot5000]
  decide +kernel

theorem arows5009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5009 = true := by
  rw [show A10K2.u5009 = KTree.node A10K2.u5005 (nat_lit 76829119) (nat_lit 11941556649) (nat_lit 0) A10K2.u5008 from rfl, allE_node, arows5005, irow5009, arows5008]
  all_goals rfl

theorem atot5009 : totK PA10K2 A10K2.u5009 = [0, 2304062504933, 10642744804166, 15840583441815, 8132159824416, 1259983336304, 44026197503, 0, 0, 0] := by
  rw [show A10K2.u5009 = KTree.node A10K2.u5005 (nat_lit 76829119) (nat_lit 11941556649) (nat_lit 0) A10K2.u5008 from rfl, totK_node, atot5005, atot5008]
  decide +kernel

theorem arows5016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5016 = true := by
  rw [show A10K2.u5016 = KTree.node A10K2.u5012 (nat_lit 76896915) (nat_lit 10772774460) (nat_lit 0) A10K2.u5015 from rfl, allE_node, arows5012, irow5016, arows5015]
  all_goals rfl

theorem atot5016 : totK PA10K2 A10K2.u5016 = [0, 1988256862423, 9762035701677, 15829424623193, 9023469131527, 1561931577886, 69384189482, 0, 0, 0] := by
  rw [show A10K2.u5016 = KTree.node A10K2.u5012 (nat_lit 76896915) (nat_lit 10772774460) (nat_lit 0) A10K2.u5015 from rfl, totK_node, atot5012, atot5015]
  decide +kernel

theorem arows5025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5025 = true := by
  rw [show A10K2.u5025 = KTree.node A10K2.u5021 (nat_lit 76956882) (nat_lit 15570890012) (nat_lit 0) A10K2.u5024 from rfl, allE_node, arows5021, irow5025, arows5024]
  all_goals rfl

theorem atot5025 : totK PA10K2 A10K2.u5025 = [0, 1596932877270, 8768425115569, 15777174582333, 9707698323895, 1724839965297, 93836009804, 0, 0, 0] := by
  rw [show A10K2.u5025 = KTree.node A10K2.u5021 (nat_lit 76956882) (nat_lit 15570890012) (nat_lit 0) A10K2.u5024 from rfl, totK_node, atot5021, atot5024]
  decide +kernel

theorem arows5032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5032 = true := by
  rw [show A10K2.u5032 = KTree.node A10K2.u5028 (nat_lit 77595396) (nat_lit 12847346766) (nat_lit 0) A10K2.u5031 from rfl, allE_node, arows5028, irow5032, arows5031]
  all_goals rfl

theorem atot5032 : totK PA10K2 A10K2.u5032 = [0, 1591502913366, 7688657659949, 13877861514828, 10810668681329, 3226194685008, 358422165524, 6354482628, 0, 0] := by
  rw [show A10K2.u5032 = KTree.node A10K2.u5028 (nat_lit 77595396) (nat_lit 12847346766) (nat_lit 0) A10K2.u5031 from rfl, totK_node, atot5028, atot5031]
  decide +kernel

theorem arows5040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5040 = true := by
  rw [show A10K2.u5040 = KTree.node A10K2.u5036 (nat_lit 77627794) (nat_lit 7327506257) (nat_lit 0) A10K2.u5039 from rfl, allE_node, arows5036, irow5040, arows5039]
  all_goals rfl

theorem atot5040 : totK PA10K2 A10K2.u5040 = [0, 625789152892, 5469370815714, 13809761957573, 13113334069935, 4713090986470, 659350623386, 30650496230, 0, 0] := by
  rw [show A10K2.u5040 = KTree.node A10K2.u5036 (nat_lit 77627794) (nat_lit 7327506257) (nat_lit 0) A10K2.u5039 from rfl, totK_node, atot5036, atot5039]
  decide +kernel

theorem arows5047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5047 = true := by
  rw [show A10K2.u5047 = KTree.node A10K2.u5043 (nat_lit 77729792) (nat_lit 15792662511) (nat_lit 0) A10K2.u5046 from rfl, allE_node, arows5043, irow5047, arows5046]
  all_goals rfl

theorem atot5047 : totK PA10K2 A10K2.u5047 = [0, 1612131783541, 7758043929622, 14098051904222, 11243146586037, 3375671797176, 311043194441, 5546304973, 0, 0] := by
  rw [show A10K2.u5047 = KTree.node A10K2.u5043 (nat_lit 77729792) (nat_lit 15792662511) (nat_lit 0) A10K2.u5046 from rfl, totK_node, atot5043, atot5046]
  decide +kernel

theorem arows5057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5057 = true := by
  rw [show A10K2.u5057 = KTree.node A10K2.u5053 (nat_lit 77768042) (nat_lit 9965998097) (nat_lit 0) A10K2.u5056 from rfl, allE_node, arows5053, irow5057, arows5056]
  all_goals rfl

theorem atot5057 : totK PA10K2 A10K2.u5057 = [0, 846021683340, 5911033834120, 13911482273072, 12810718935653, 3866823608862, 393214209434, 6354482628, 0, 0] := by
  rw [show A10K2.u5057 = KTree.node A10K2.u5053 (nat_lit 77768042) (nat_lit 9965998097) (nat_lit 0) A10K2.u5056 from rfl, totK_node, atot5053, atot5056]
  decide +kernel

theorem arows5064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5064 = true := by
  rw [show A10K2.u5064 = KTree.node A10K2.u5060 (nat_lit 77820494) (nat_lit 10059891680) (nat_lit 0) A10K2.u5063 from rfl, allE_node, arows5060, irow5064, arows5063]
  all_goals rfl

theorem atot5064 : totK PA10K2 A10K2.u5064 = [0, 1057749846530, 6664514841657, 14552415461419, 12817263167753, 4195220960704, 420747725091, 6904928264, 0, 0] := by
  rw [show A10K2.u5064 = KTree.node A10K2.u5060 (nat_lit 77820494) (nat_lit 10059891680) (nat_lit 0) A10K2.u5063 from rfl, totK_node, atot5060, atot5063]
  decide +kernel

theorem arows5072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5072 = true := by
  rw [show A10K2.u5072 = KTree.node A10K2.u5068 (nat_lit 78201645) (nat_lit 6564919360) (nat_lit 0) A10K2.u5071 from rfl, allE_node, arows5068, irow5072, arows5071]
  all_goals rfl

theorem atot5072 : totK PA10K2 A10K2.u5072 = [0, 2223525989148, 10212321470228, 15695742773254, 8950565747226, 1729198692585, 89011749953, 0, 0, 0] := by
  rw [show A10K2.u5072 = KTree.node A10K2.u5068 (nat_lit 78201645) (nat_lit 6564919360) (nat_lit 0) A10K2.u5071 from rfl, totK_node, atot5068, atot5071]
  decide +kernel

theorem arows5079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5079 = true := by
  rw [show A10K2.u5079 = KTree.node A10K2.u5075 (nat_lit 78234112) (nat_lit 15163022925) (nat_lit 0) A10K2.u5078 from rfl, allE_node, arows5075, irow5079, arows5078]
  all_goals rfl

theorem atot5079 : totK PA10K2 A10K2.u5079 = [0, 272465788330, 3388610609893, 11673790282536, 15252949641839, 6828411493380, 935738490154, 37204059898, 0, 0] := by
  rw [show A10K2.u5079 = KTree.node A10K2.u5075 (nat_lit 78234112) (nat_lit 15163022925) (nat_lit 0) A10K2.u5078 from rfl, totK_node, atot5075, atot5078]
  decide +kernel

theorem arows5088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5088 = true := by
  rw [show A10K2.u5088 = KTree.node A10K2.u5084 (nat_lit 78264535) (nat_lit 10619523044) (nat_lit 0) A10K2.u5087 from rfl, allE_node, arows5084, irow5088, arows5087]
  all_goals rfl

theorem atot5088 : totK PA10K2 A10K2.u5088 = [0, 1880827869746, 9429645854506, 15663037982978, 9307497983171, 1712556835294, 93728942688, 0, 0, 0] := by
  rw [show A10K2.u5088 = KTree.node A10K2.u5084 (nat_lit 78264535) (nat_lit 10619523044) (nat_lit 0) A10K2.u5087 from rfl, totK_node, atot5084, atot5087]
  decide +kernel

theorem arows5095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5095 = true := by
  rw [show A10K2.u5095 = KTree.node A10K2.u5091 (nat_lit 78304517) (nat_lit 6919523439) (nat_lit 0) A10K2.u5094 from rfl, allE_node, arows5091, irow5095, arows5094]
  all_goals rfl

theorem atot5095 : totK PA10K2 A10K2.u5095 = [0, 1061690136320, 6328799906614, 14034301271671, 12834709734690, 3921364576008, 393261774295, 6354482628, 0, 0] := by
  rw [show A10K2.u5095 = KTree.node A10K2.u5091 (nat_lit 78304517) (nat_lit 6919523439) (nat_lit 0) A10K2.u5094 from rfl, totK_node, atot5091, atot5094]
  decide +kernel

theorem arows5103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5103 = true := by
  rw [show A10K2.u5103 = KTree.node A10K2.u5099 (nat_lit 78362771) (nat_lit 10916391681) (nat_lit 0) A10K2.u5102 from rfl, allE_node, arows5099, irow5103, arows5102]
  all_goals rfl

theorem atot5103 : totK PA10K2 A10K2.u5103 = [0, 1106618669198, 6530115488415, 13990393252978, 12892761962950, 4620397242196, 469541436258, 7047025452, 0, 0] := by
  rw [show A10K2.u5103 = KTree.node A10K2.u5099 (nat_lit 78362771) (nat_lit 10916391681) (nat_lit 0) A10K2.u5102 from rfl, totK_node, atot5099, atot5102]
  decide +kernel

theorem arows5110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5110 = true := by
  rw [show A10K2.u5110 = KTree.node A10K2.u5106 (nat_lit 78671282) (nat_lit 12201568943) (nat_lit 0) A10K2.u5109 from rfl, allE_node, arows5106, irow5110, arows5109]
  all_goals rfl

theorem atot5110 : totK PA10K2 A10K2.u5110 = [0, 1242177520553, 7089248045146, 14156583771849, 11442696907717, 3600475036633, 498216724988, 30220878370, 0, 0] := by
  rw [show A10K2.u5110 = KTree.node A10K2.u5106 (nat_lit 78671282) (nat_lit 12201568943) (nat_lit 0) A10K2.u5109 from rfl, totK_node, atot5106, atot5109]
  decide +kernel

theorem arows5124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5124 = true := by
  rw [show A10K2.u5124 = KTree.node A10K2.u5120 (nat_lit 78719203) (nat_lit 10404645789) (nat_lit 0) A10K2.u5123 from rfl, allE_node, arows5120, irow5124, arows5123]
  all_goals rfl

theorem atot5124 : totK PA10K2 A10K2.u5124 = [0, 1586773631500, 7864272626509, 14232413020664, 11099754111831, 3137406788489, 283715366819, 5546304973, 0, 0] := by
  rw [show A10K2.u5124 = KTree.node A10K2.u5120 (nat_lit 78719203) (nat_lit 10404645789) (nat_lit 0) A10K2.u5123 from rfl, totK_node, atot5120, atot5123]
  decide +kernel

theorem arows5131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5131 = true := by
  rw [show A10K2.u5131 = KTree.node A10K2.u5127 (nat_lit 78753211) (nat_lit 6967763597) (nat_lit 0) A10K2.u5130 from rfl, allE_node, arows5127, irow5131, arows5130]
  all_goals rfl

theorem atot5131 : totK PA10K2 A10K2.u5131 = [0, 461607179050, 4319692941491, 12723267495808, 14256777363823, 5571902513387, 754656448020, 30647824416, 0, 0] := by
  rw [show A10K2.u5131 = KTree.node A10K2.u5127 (nat_lit 78753211) (nat_lit 6967763597) (nat_lit 0) A10K2.u5130 from rfl, totK_node, atot5127, atot5130]
  decide +kernel

theorem arows5139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5139 = true := by
  rw [show A10K2.u5139 = KTree.node A10K2.u5135 (nat_lit 78783990) (nat_lit 13758123434) (nat_lit 0) A10K2.u5138 from rfl, allE_node, arows5135, irow5139, arows5138]
  all_goals rfl

theorem atot5139 : totK PA10K2 A10K2.u5139 = [0, 2332949133701, 10165352780752, 15184655617148, 8818407714332, 1657538219221, 89851414766, 0, 0, 0] := by
  rw [show A10K2.u5139 = KTree.node A10K2.u5135 (nat_lit 78783990) (nat_lit 13758123434) (nat_lit 0) A10K2.u5138 from rfl, totK_node, atot5135, atot5138]
  decide +kernel

theorem arows5146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5146 = true := by
  rw [show A10K2.u5146 = KTree.node A10K2.u5142 (nat_lit 78818483) (nat_lit 10186011321) (nat_lit 0) A10K2.u5145 from rfl, allE_node, arows5142, irow5146, arows5145]
  all_goals rfl

theorem atot5146 : totK PA10K2 A10K2.u5146 = [0, 0, 4002777885361, 14236965671400, 14707892779699, 4361464663284, 425340206809, 6354482628, 0, 0] := by
  rw [show A10K2.u5146 = KTree.node A10K2.u5142 (nat_lit 78818483) (nat_lit 10186011321) (nat_lit 0) A10K2.u5145 from rfl, totK_node, atot5142, atot5145]
  decide +kernel

theorem arows5155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5155 = true := by
  rw [show A10K2.u5155 = KTree.node A10K2.u5151 (nat_lit 78927879) (nat_lit 10628172283) (nat_lit 0) A10K2.u5154 from rfl, allE_node, arows5151, irow5155, arows5154]
  all_goals rfl

theorem atot5155 : totK PA10K2 A10K2.u5155 = [0, 0, 2257779650695, 10556230258975, 15983404795231, 7778921953635, 1181952227531, 62042702734, 0, 0] := by
  rw [show A10K2.u5155 = KTree.node A10K2.u5151 (nat_lit 78927879) (nat_lit 10628172283) (nat_lit 0) A10K2.u5154 from rfl, totK_node, atot5151, atot5154]
  decide +kernel

theorem arows5162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5162 = true := by
  rw [show A10K2.u5162 = KTree.node A10K2.u5158 (nat_lit 79036677) (nat_lit 6887253644) (nat_lit 0) A10K2.u5161 from rfl, allE_node, arows5158, irow5162, arows5161]
  all_goals rfl

theorem atot5162 : totK PA10K2 A10K2.u5162 = [0, 0, 2716759235402, 11585506827398, 15603794436938, 6843044735545, 995541359154, 42147406732, 0, 0] := by
  rw [show A10K2.u5162 = KTree.node A10K2.u5158 (nat_lit 79036677) (nat_lit 6887253644) (nat_lit 0) A10K2.u5161 from rfl, totK_node, atot5158, atot5161]
  decide +kernel

theorem arows5170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5170 = true := by
  rw [show A10K2.u5170 = KTree.node A10K2.u5166 (nat_lit 79069224) (nat_lit 12863397079) (nat_lit 0) A10K2.u5169 from rfl, allE_node, arows5166, irow5170, arows5169]
  all_goals rfl

theorem atot5170 : totK PA10K2 A10K2.u5170 = [0, 0, 844597474735, 6811508314752, 15488944383629, 11162351918912, 2477953904150, 150351458370, 0, 0] := by
  rw [show A10K2.u5170 = KTree.node A10K2.u5166 (nat_lit 79069224) (nat_lit 12863397079) (nat_lit 0) A10K2.u5169 from rfl, totK_node, atot5166, atot5169]
  decide +kernel

theorem arows5177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5177 = true := by
  rw [show A10K2.u5177 = KTree.node A10K2.u5173 (nat_lit 83893252) (nat_lit 10385418866) (nat_lit 0) A10K2.u5176 from rfl, allE_node, arows5173, irow5177, arows5176]
  all_goals rfl

theorem atot5177 : totK PA10K2 A10K2.u5177 = [0, 2338692983822, 9769411963070, 13417334437510, 7353336977661, 3316008114362, 1561268114732, 265614550179, 6354482628, 0] := by
  rw [show A10K2.u5177 = KTree.node A10K2.u5173 (nat_lit 83893252) (nat_lit 10385418866) (nat_lit 0) A10K2.u5176 from rfl, totK_node, atot5173, atot5176]
  decide +kernel

theorem arows5187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5187 = true := by
  rw [show A10K2.u5187 = KTree.node A10K2.u5183 (nat_lit 83923534) (nat_lit 9966385053) (nat_lit 0) A10K2.u5186 from rfl, allE_node, arows5183, irow5187, arows5186]
  all_goals rfl

theorem atot5187 : totK PA10K2 A10K2.u5187 = [0, 0, 3134251169278, 12370141055959, 15441557347882, 6424833425989, 880048568284, 36196801203, 0, 0] := by
  rw [show A10K2.u5187 = KTree.node A10K2.u5183 (nat_lit 83923534) (nat_lit 9966385053) (nat_lit 0) A10K2.u5186 from rfl, totK_node, atot5183, atot5186]
  decide +kernel

theorem arows5194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5194 = true := by
  rw [show A10K2.u5194 = KTree.node A10K2.u5190 (nat_lit 84027028) (nat_lit 11980330599) (nat_lit 0) A10K2.u5193 from rfl, allE_node, arows5190, irow5194, arows5193]
  all_goals rfl

theorem atot5194 : totK PA10K2 A10K2.u5194 = [0, 2056441471990, 9709946614033, 15314427965895, 9117754530285, 1908098786166, 105199719046, 0, 0, 0] := by
  rw [show A10K2.u5194 = KTree.node A10K2.u5190 (nat_lit 84027028) (nat_lit 11980330599) (nat_lit 0) A10K2.u5193 from rfl, totK_node, atot5190, atot5193]
  decide +kernel

theorem arows5202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5202 = true := by
  rw [show A10K2.u5202 = KTree.node A10K2.u5198 (nat_lit 84068507) (nat_lit 10015913925) (nat_lit 0) A10K2.u5201 from rfl, allE_node, arows5198, irow5202, arows5201]
  all_goals rfl

theorem atot5202 : totK PA10K2 A10K2.u5202 = [0, 809589589006, 5634213051419, 13850356784061, 13264480315916, 4188733179436, 419000546485, 6354482628, 0, 0] := by
  rw [show A10K2.u5202 = KTree.node A10K2.u5198 (nat_lit 84068507) (nat_lit 10015913925) (nat_lit 0) A10K2.u5201 from rfl, totK_node, atot5198, atot5201]
  decide +kernel

theorem arows5209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5209 = true := by
  rw [show A10K2.u5209 = KTree.node A10K2.u5205 (nat_lit 84114597) (nat_lit 11933677) (nat_lit 0) A10K2.u5208 from rfl, allE_node, arows5205, irow5209, arows5208]
  all_goals rfl

theorem atot5209 : totK PA10K2 A10K2.u5209 = [0, 1078827900697, 6431677648702, 14022296048079, 13241265811234, 4784370418779, 476599559859, 6904928264, 0, 0] := by
  rw [show A10K2.u5209 = KTree.node A10K2.u5205 (nat_lit 84114597) (nat_lit 11933677) (nat_lit 0) A10K2.u5208 from rfl, totK_node, atot5205, atot5208]
  decide +kernel

theorem arows5218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5218 = true := by
  rw [show A10K2.u5218 = KTree.node A10K2.u5214 (nat_lit 84150368) (nat_lit 13699160110) (nat_lit 0) A10K2.u5217 from rfl, allE_node, arows5214, irow5218, arows5217]
  all_goals rfl

theorem atot5218 : totK PA10K2 A10K2.u5218 = [0, 0, 2391377490038, 10620894728580, 15740763351579, 8616145223069, 1532779165748, 70685906944, 0, 0] := by
  rw [show A10K2.u5218 = KTree.node A10K2.u5214 (nat_lit 84150368) (nat_lit 13699160110) (nat_lit 0) A10K2.u5217 from rfl, totK_node, atot5214, atot5217]
  decide +kernel

theorem arows5225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5225 = true := by
  rw [show A10K2.u5225 = KTree.node A10K2.u5221 (nat_lit 84181439) (nat_lit 14166159072) (nat_lit 0) A10K2.u5224 from rfl, allE_node, arows5221, irow5225, arows5224]
  all_goals rfl

theorem atot5225 : totK PA10K2 A10K2.u5225 = [0, 0, 740599976690, 5644612340594, 13815180827929, 12719948088995, 4396604339788, 647349928420, 30605747850, 0] := by
  rw [show A10K2.u5225 = KTree.node A10K2.u5221 (nat_lit 84181439) (nat_lit 14166159072) (nat_lit 0) A10K2.u5224 from rfl, totK_node, atot5221, atot5224]
  decide +kernel

theorem arows5233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5233 = true := by
  rw [show A10K2.u5233 = KTree.node A10K2.u5229 (nat_lit 84283456) (nat_lit 15482570017) (nat_lit 0) A10K2.u5232 from rfl, allE_node, arows5229, irow5233, arows5232]
  all_goals rfl

theorem atot5233 : totK PA10K2 A10K2.u5233 = [0, 0, 1846750146465, 8499946327442, 14338656160407, 10243016290348, 2845358638064, 277554211460, 5528811039, 0] := by
  rw [show A10K2.u5233 = KTree.node A10K2.u5229 (nat_lit 84283456) (nat_lit 15482570017) (nat_lit 0) A10K2.u5232 from rfl, totK_node, atot5229, atot5232]
  decide +kernel

theorem arows5240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5240 = true := by
  rw [show A10K2.u5240 = KTree.node A10K2.u5236 (nat_lit 84328722) (nat_lit 11874975076) (nat_lit 0) A10K2.u5239 from rfl, allE_node, arows5236, irow5240, arows5239]
  all_goals rfl

theorem atot5240 : totK PA10K2 A10K2.u5240 = [0, 0, 1014981732574, 6829454151546, 14682575833358, 11730615560794, 3149470325993, 274073213902, 5676195732, 0] := by
  rw [show A10K2.u5240 = KTree.node A10K2.u5236 (nat_lit 84328722) (nat_lit 11874975076) (nat_lit 0) A10K2.u5239 from rfl, totK_node, atot5236, atot5239]
  decide +kernel

theorem arows5251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5251 = true := by
  rw [show A10K2.u5251 = KTree.node A10K2.u5247 (nat_lit 84374114) (nat_lit 2501064225) (nat_lit 0) A10K2.u5250 from rfl, allE_node, arows5247, irow5251, arows5250]
  all_goals rfl

theorem atot5251 : totK PA10K2 A10K2.u5251 = [0, 833436429740, 4946305267513, 11709595711435, 13528223788809, 7095604421155, 1285706991959, 61854180319, 0, 0] := by
  rw [show A10K2.u5251 = KTree.node A10K2.u5247 (nat_lit 84374114) (nat_lit 2501064225) (nat_lit 0) A10K2.u5250 from rfl, totK_node, atot5247, atot5250]
  decide +kernel

theorem arows5258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5258 = true := by
  rw [show A10K2.u5258 = KTree.node A10K2.u5254 (nat_lit 84963654) (nat_lit 10914992213) (nat_lit 0) A10K2.u5257 from rfl, allE_node, arows5254, irow5258, arows5257]
  all_goals rfl

theorem atot5258 : totK PA10K2 A10K2.u5258 = [0, 1322336744556, 7064798423386, 13598184355806, 11507567591401, 4230656105770, 630013315076, 30650496230, 0, 0] := by
  rw [show A10K2.u5258 = KTree.node A10K2.u5254 (nat_lit 84963654) (nat_lit 10914992213) (nat_lit 0) A10K2.u5257 from rfl, totK_node, atot5254, atot5257]
  decide +kernel

theorem arows5266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5266 = true := by
  rw [show A10K2.u5266 = KTree.node A10K2.u5262 (nat_lit 85010184) (nat_lit 7304398159) (nat_lit 0) A10K2.u5265 from rfl, allE_node, arows5262, irow5266, arows5265]
  all_goals rfl

theorem atot5266 : totK PA10K2 A10K2.u5266 = [0, 1542377451919, 7762236932620, 14279554985038, 11318697701705, 3423315478352, 319489491730, 5546304973, 0, 0] := by
  rw [show A10K2.u5266 = KTree.node A10K2.u5262 (nat_lit 85010184) (nat_lit 7304398159) (nat_lit 0) A10K2.u5265 from rfl, totK_node, atot5262, atot5265]
  decide +kernel

theorem arows5273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5273 = true := by
  rw [show A10K2.u5273 = KTree.node A10K2.u5269 (nat_lit 85050523) (nat_lit 10063092638) (nat_lit 0) A10K2.u5272 from rfl, allE_node, arows5269, irow5273, arows5272]
  all_goals rfl

theorem atot5273 : totK PA10K2 A10K2.u5273 = [0, 762214156616, 5220461436404, 12829217331096, 13232676113369, 5385392523553, 753467472596, 37204059898, 0, 0] := by
  rw [show A10K2.u5273 = KTree.node A10K2.u5269 (nat_lit 85050523) (nat_lit 10063092638) (nat_lit 0) A10K2.u5272 from rfl, totK_node, atot5269, atot5272]
  decide +kernel

theorem arows5282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5282 = true := by
  rw [show A10K2.u5282 = KTree.node A10K2.u5278 (nat_lit 85083009) (nat_lit 10225672940) (nat_lit 0) A10K2.u5281 from rfl, allE_node, arows5278, irow5282, arows5281]
  all_goals rfl

theorem atot5282 : totK PA10K2 A10K2.u5282 = [0, 1491872713986, 8338435562371, 15504729797418, 10535272188067, 2197667075753, 107738090636, 0, 0, 0] := by
  rw [show A10K2.u5282 = KTree.node A10K2.u5278 (nat_lit 85083009) (nat_lit 10225672940) (nat_lit 0) A10K2.u5281 from rfl, totK_node, atot5278, atot5281]
  decide +kernel

theorem arows5289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5289 = true := by
  rw [show A10K2.u5289 = KTree.node A10K2.u5285 (nat_lit 85197120) (nat_lit 14925203453) (nat_lit 0) A10K2.u5288 from rfl, allE_node, arows5285, irow5289, arows5288]
  all_goals rfl

theorem atot5289 : totK PA10K2 A10K2.u5289 = [0, 0, 2686777921818, 11507979031707, 15676484791461, 6976379982302, 1002570163186, 37172849495, 0, 0] := by
  rw [show A10K2.u5289 = KTree.node A10K2.u5285 (nat_lit 85197120) (nat_lit 14925203453) (nat_lit 0) A10K2.u5288 from rfl, totK_node, atot5285, atot5288]
  decide +kernel

theorem arows5297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5297 = true := by
  rw [show A10K2.u5297 = KTree.node A10K2.u5293 (nat_lit 85272388) (nat_lit 11673305322) (nat_lit 0) A10K2.u5296 from rfl, allE_node, arows5293, irow5297, arows5296]
  all_goals rfl

theorem atot5297 : totK PA10K2 A10K2.u5297 = [0, 0, 2284156943827, 10732611680980, 16236345332043, 8202934242255, 1177597405298, 44660404486, 0, 0] := by
  rw [show A10K2.u5297 = KTree.node A10K2.u5293 (nat_lit 85272388) (nat_lit 11673305322) (nat_lit 0) A10K2.u5296 from rfl, totK_node, atot5293, atot5296]
  decide +kernel

theorem arows5304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5304 = true := by
  rw [show A10K2.u5304 = KTree.node A10K2.u5300 (nat_lit 85337785) (nat_lit 1474703627) (nat_lit 0) A10K2.u5303 from rfl, allE_node, arows5300, irow5304, arows5303]
  all_goals rfl

theorem atot5304 : totK PA10K2 A10K2.u5304 = [0, 0, 2251479923293, 10385530561569, 15692744573341, 8107208780437, 1329283758561, 67432810860, 0, 0] := by
  rw [show A10K2.u5304 = KTree.node A10K2.u5300 (nat_lit 85337785) (nat_lit 1474703627) (nat_lit 0) A10K2.u5303 from rfl, totK_node, atot5300, atot5303]
  decide +kernel

theorem arows5314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5314 = true := by
  rw [show A10K2.u5314 = KTree.node A10K2.u5310 (nat_lit 85378259) (nat_lit 10852665224) (nat_lit 0) A10K2.u5313 from rfl, allE_node, arows5310, irow5314, arows5313]
  all_goals rfl

theorem atot5314 : totK PA10K2 A10K2.u5314 = [0, 842822735057, 3289402214160, 6707349316259, 11777024706866, 10949346608828, 3494376058967, 384962563863, 6354482628, 0] := by
  rw [show A10K2.u5314 = KTree.node A10K2.u5310 (nat_lit 85378259) (nat_lit 10852665224) (nat_lit 0) A10K2.u5313 from rfl, totK_node, atot5310, atot5313]
  decide +kernel

theorem arows5321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5321 = true := by
  rw [show A10K2.u5321 = KTree.node A10K2.u5317 (nat_lit 85485489) (nat_lit 7628858159) (nat_lit 0) A10K2.u5320 from rfl, allE_node, arows5317, irow5321, arows5320]
  all_goals rfl

theorem atot5321 : totK PA10K2 A10K2.u5321 = [0, 1362618835023, 7819653842011, 15483338735728, 11699374599767, 2780228187256, 160381790870, 0, 0, 0] := by
  rw [show A10K2.u5321 = KTree.node A10K2.u5317 (nat_lit 85485489) (nat_lit 7628858159) (nat_lit 0) A10K2.u5320 from rfl, totK_node, atot5317, atot5320]
  decide +kernel

theorem arows5329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5329 = true := by
  rw [show A10K2.u5329 = KTree.node A10K2.u5325 (nat_lit 85518070) (nat_lit 15309099911) (nat_lit 0) A10K2.u5328 from rfl, allE_node, arows5325, irow5329, arows5328]
  all_goals rfl

theorem atot5329 : totK PA10K2 A10K2.u5329 = [0, 1068376898294, 5879884860464, 12670217723678, 12840442640572, 5509723004722, 847413409177, 36196801203, 0, 0] := by
  rw [show A10K2.u5329 = KTree.node A10K2.u5325 (nat_lit 85518070) (nat_lit 15309099911) (nat_lit 0) A10K2.u5328 from rfl, totK_node, atot5325, atot5328]
  decide +kernel

theorem arows5336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5336 = true := by
  rw [show A10K2.u5336 = KTree.node A10K2.u5332 (nat_lit 85685176) (nat_lit 13840218535) (nat_lit 0) A10K2.u5335 from rfl, allE_node, arows5332, irow5336, arows5335]
  all_goals rfl

theorem atot5336 : totK PA10K2 A10K2.u5336 = [0, 1175483150104, 6911862322495, 14431055814289, 12639559385509, 4297271972476, 443711391119, 6904928264, 0, 0] := by
  rw [show A10K2.u5336 = KTree.node A10K2.u5332 (nat_lit 85685176) (nat_lit 13840218535) (nat_lit 0) A10K2.u5335 from rfl, totK_node, atot5332, atot5335]
  decide +kernel

theorem arows5345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5345 = true := by
  rw [show A10K2.u5345 = KTree.node A10K2.u5341 (nat_lit 85717560) (nat_lit 14373523239) (nat_lit 0) A10K2.u5344 from rfl, allE_node, arows5341, irow5345, arows5344]
  all_goals rfl

theorem atot5345 : totK PA10K2 A10K2.u5345 = [0, 0, 2126706739296, 10024008607838, 15938362818076, 9495630971036, 1764410932447, 93490405862, 0, 0] := by
  rw [show A10K2.u5345 = KTree.node A10K2.u5341 (nat_lit 85717560) (nat_lit 14373523239) (nat_lit 0) A10K2.u5344 from rfl, totK_node, atot5341, atot5344]
  decide +kernel

theorem arows5352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5352 = true := by
  rw [show A10K2.u5352 = KTree.node A10K2.u5348 (nat_lit 85749860) (nat_lit 11199207806) (nat_lit 0) A10K2.u5351 from rfl, allE_node, arows5348, irow5352, arows5351]
  all_goals rfl

theorem atot5352 : totK PA10K2 A10K2.u5352 = [0, 0, 1362618835023, 7575903438424, 14691935074970, 11608761530886, 3558663706951, 374950387831, 7007974415, 0] := by
  rw [show A10K2.u5352 = KTree.node A10K2.u5348 (nat_lit 85749860) (nat_lit 11199207806) (nat_lit 0) A10K2.u5351 from rfl, totK_node, atot5348, atot5351]
  decide +kernel

theorem arows5360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5360 = true := by
  rw [show A10K2.u5360 = KTree.node A10K2.u5356 (nat_lit 85922148) (nat_lit 11863823779) (nat_lit 0) A10K2.u5359 from rfl, allE_node, arows5356, irow5360, arows5359]
  all_goals rfl

theorem atot5360 : totK PA10K2 A10K2.u5360 = [0, 0, 1928684513738, 9639923155364, 16313913530368, 10112974606873, 1801196145656, 74078704593, 0, 0] := by
  rw [show A10K2.u5360 = KTree.node A10K2.u5356 (nat_lit 85922148) (nat_lit 11863823779) (nat_lit 0) A10K2.u5359 from rfl, totK_node, atot5356, atot5359]
  decide +kernel

theorem arows5367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5367 = true := by
  rw [show A10K2.u5367 = KTree.node A10K2.u5363 (nat_lit 88682206) (nat_lit 11283310526) (nat_lit 0) A10K2.u5366 from rfl, allE_node, arows5363, irow5367, arows5366]
  all_goals rfl

theorem atot5367 : totK PA10K2 A10K2.u5367 = [0, 1600415090483, 7743049655212, 13265570544945, 10414886160764, 4776186424442, 1044019081342, 62833682686, 0, 0] := by
  rw [show A10K2.u5367 = KTree.node A10K2.u5363 (nat_lit 88682206) (nat_lit 11283310526) (nat_lit 0) A10K2.u5366 from rfl, totK_node, atot5363, atot5366]
  decide +kernel

theorem arows5379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5379 = true := by
  rw [show A10K2.u5379 = KTree.node A10K2.u5375 (nat_lit 88713499) (nat_lit 9964074265) (nat_lit 0) A10K2.u5378 from rfl, allE_node, arows5375, irow5379, arows5378]
  all_goals rfl

theorem atot5379 : totK PA10K2 A10K2.u5379 = [0, 743410903023, 5075290742992, 12884884249140, 13762797002131, 5466445457168, 724298552071, 31082886609, 0, 0] := by
  rw [show A10K2.u5379 = KTree.node A10K2.u5375 (nat_lit 88713499) (nat_lit 9964074265) (nat_lit 0) A10K2.u5378 from rfl, totK_node, atot5375, atot5378]
  decide +kernel

theorem arows5386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5386 = true := by
  rw [show A10K2.u5386 = KTree.node A10K2.u5382 (nat_lit 88742570) (nat_lit 10163103829) (nat_lit 0) A10K2.u5385 from rfl, allE_node, arows5382, irow5386, arows5385]
  all_goals rfl

theorem atot5386 : totK PA10K2 A10K2.u5386 = [0, 1760121724390, 8264786628254, 14091338683278, 10649915645191, 3305047579874, 317312245023, 6121173289, 0, 0] := by
  rw [show A10K2.u5386 = KTree.node A10K2.u5382 (nat_lit 88742570) (nat_lit 10163103829) (nat_lit 0) A10K2.u5385 from rfl, totK_node, atot5382, atot5385]
  decide +kernel

theorem arows5394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5394 = true := by
  rw [show A10K2.u5394 = KTree.node A10K2.u5390 (nat_lit 88780023) (nat_lit 14557710542) (nat_lit 0) A10K2.u5393 from rfl, allE_node, arows5390, irow5394, arows5393]
  all_goals rfl

theorem atot5394 : totK PA10K2 A10K2.u5394 = [0, 746297413151, 5760728120148, 14175442268707, 13092014273401, 3958560275411, 393727296452, 6354482628, 0, 0] := by
  rw [show A10K2.u5394 = KTree.node A10K2.u5390 (nat_lit 88780023) (nat_lit 14557710542) (nat_lit 0) A10K2.u5393 from rfl, totK_node, atot5390, atot5393]
  decide +kernel

theorem arows5401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5401 = true := by
  rw [show A10K2.u5401 = KTree.node A10K2.u5397 (nat_lit 88829335) (nat_lit 14616934806) (nat_lit 0) A10K2.u5400 from rfl, allE_node, arows5397, irow5401, arows5400]
  all_goals rfl

theorem atot5401 : totK PA10K2 A10K2.u5401 = [0, 1444265333701, 8013613835986, 15325617153083, 11761997393514, 3272650466984, 229492418292, 0, 0, 0] := by
  rw [show A10K2.u5401 = KTree.node A10K2.u5397 (nat_lit 88829335) (nat_lit 14616934806) (nat_lit 0) A10K2.u5400 from rfl, totK_node, atot5397, atot5400]
  decide +kernel

theorem arows5410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5410 = true := by
  rw [show A10K2.u5410 = KTree.node A10K2.u5406 (nat_lit 88864667) (nat_lit 8264713067) (nat_lit 0) A10K2.u5409 from rfl, allE_node, arows5406, irow5410, arows5409]
  all_goals rfl

theorem atot5410 : totK PA10K2 A10K2.u5410 = [0, 0, 1983826722996, 9674823275449, 16054431249057, 9896357036478, 1817827985339, 80737018769, 0, 0] := by
  rw [show A10K2.u5410 = KTree.node A10K2.u5406 (nat_lit 88864667) (nat_lit 8264713067) (nat_lit 0) A10K2.u5409 from rfl, totK_node, atot5406, atot5409]
  decide +kernel

theorem arows5417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5417 = true := by
  rw [show A10K2.u5417 = KTree.node A10K2.u5413 (nat_lit 88961466) (nat_lit 12874240221) (nat_lit 0) A10K2.u5416 from rfl, allE_node, arows5413, irow5417, arows5416]
  all_goals rfl

theorem atot5417 : totK PA10K2 A10K2.u5417 = [0, 0, 1382040637232, 7511938194279, 14216345729300, 11046872101099, 3717927222694, 538133810471, 25565504801, 0] := by
  rw [show A10K2.u5417 = KTree.node A10K2.u5413 (nat_lit 88961466) (nat_lit 12874240221) (nat_lit 0) A10K2.u5416 from rfl, totK_node, atot5413, atot5416]
  decide +kernel

theorem arows5425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5425 = true := by
  rw [show A10K2.u5425 = KTree.node A10K2.u5421 (nat_lit 88997966) (nat_lit 7555640894) (nat_lit 128) A10K2.u5424 from rfl, allE_node, arows5421, irow5425, arows5424]
  all_goals rfl

theorem atot5425 : totK PA10K2 A10K2.u5425 = [0, 0, 1268414326845, 7095625713571, 14143092343589, 11668582633476, 3623478652240, 405652602360, 11138589073, 0] := by
  rw [show A10K2.u5425 = KTree.node A10K2.u5421 (nat_lit 88997966) (nat_lit 7555640894) (nat_lit 128) A10K2.u5424 from rfl, totK_node, atot5421, atot5424]
  decide +kernel

theorem arows5432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5432 = true := by
  rw [show A10K2.u5432 = KTree.node A10K2.u5428 (nat_lit 89040059) (nat_lit 7200714921) (nat_lit 0) A10K2.u5431 from rfl, allE_node, arows5428, irow5432, arows5431]
  all_goals rfl

theorem atot5432 : totK PA10K2 A10K2.u5432 = [0, 0, 910649247302, 6208490240146, 14440120800229, 12464824449228, 3345831443567, 285850577215, 6239673734, 0] := by
  rw [show A10K2.u5432 = KTree.node A10K2.u5428 (nat_lit 89040059) (nat_lit 7200714921) (nat_lit 0) A10K2.u5431 from rfl, totK_node, atot5428, atot5431]
  decide +kernel

theorem arows5442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5442 = true := by
  rw [show A10K2.u5442 = KTree.node A10K2.u5438 (nat_lit 89088561) (nat_lit 9956268782) (nat_lit 0) A10K2.u5441 from rfl, allE_node, arows5438, irow5442, arows5441]
  all_goals rfl

theorem atot5442 : totK PA10K2 A10K2.u5442 = [0, 597780859188, 3859009552222, 10693429086673, 14556154858343, 8565781818134, 1620624879664, 74160186325, 0, 0] := by
  rw [show A10K2.u5442 = KTree.node A10K2.u5438 (nat_lit 89088561) (nat_lit 9956268782) (nat_lit 0) A10K2.u5441 from rfl, totK_node, atot5438, atot5441]
  decide +kernel

theorem arows5449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5449 = true := by
  rw [show A10K2.u5449 = KTree.node A10K2.u5445 (nat_lit 89151840) (nat_lit 12249626433) (nat_lit 0) A10K2.u5448 from rfl, allE_node, arows5445, irow5449, arows5448]
  all_goals rfl

theorem atot5449 : totK PA10K2 A10K2.u5449 = [0, 925615260218, 6453658704410, 14294152026647, 12117274864078, 3951927092888, 545951578125, 30650496230, 0, 0] := by
  rw [show A10K2.u5449 = KTree.node A10K2.u5445 (nat_lit 89151840) (nat_lit 12249626433) (nat_lit 0) A10K2.u5448 from rfl, totK_node, atot5445, atot5448]
  decide +kernel

theorem arows5457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5457 = true := by
  rw [show A10K2.u5457 = KTree.node A10K2.u5453 (nat_lit 89209384) (nat_lit 9933918135) (nat_lit 0) A10K2.u5456 from rfl, allE_node, arows5453, irow5457, arows5456]
  all_goals rfl

theorem atot5457 : totK PA10K2 A10K2.u5457 = [0, 2161736226052, 9392948790003, 14508608953534, 9526767022840, 2519958417763, 237206624312, 5546304973, 0, 0] := by
  rw [show A10K2.u5457 = KTree.node A10K2.u5453 (nat_lit 89209384) (nat_lit 9933918135) (nat_lit 0) A10K2.u5456 from rfl, totK_node, atot5453, atot5456]
  decide +kernel

theorem arows5464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5464 = true := by
  rw [show A10K2.u5464 = KTree.node A10K2.u5460 (nat_lit 89242272) (nat_lit 6655669496) (nat_lit 0) A10K2.u5463 from rfl, allE_node, arows5460, irow5464, arows5463]
  all_goals rfl

theorem atot5464 : totK PA10K2 A10K2.u5464 = [0, 0, 2927474039157, 12013108306976, 15697456302558, 6882442435914, 927126954678, 37204059898, 0, 0] := by
  rw [show A10K2.u5464 = KTree.node A10K2.u5460 (nat_lit 89242272) (nat_lit 6655669496) (nat_lit 0) A10K2.u5463 from rfl, totK_node, atot5460, atot5463]
  decide +kernel

theorem arows5473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5473 = true := by
  rw [show A10K2.u5473 = KTree.node A10K2.u5469 (nat_lit 89272051) (nat_lit 9156035615) (nat_lit 0) A10K2.u5472 from rfl, allE_node, arows5469, irow5473, arows5472]
  all_goals rfl

theorem atot5473 : totK PA10K2 A10K2.u5473 = [0, 2254573189466, 10441594129477, 15634407935320, 8328793270185, 1534741219162, 92796362578, 0, 0, 0] := by
  rw [show A10K2.u5473 = KTree.node A10K2.u5469 (nat_lit 89272051) (nat_lit 9156035615) (nat_lit 0) A10K2.u5472 from rfl, totK_node, atot5469, atot5472]
  decide +kernel

theorem arows5480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5480 = true := by
  rw [show A10K2.u5480 = KTree.node A10K2.u5476 (nat_lit 89310960) (nat_lit 858117379) (nat_lit 0) A10K2.u5479 from rfl, allE_node, arows5476, irow5480, arows5479]
  all_goals rfl

theorem atot5480 : totK PA10K2 A10K2.u5480 = [0, 0, 3006225286978, 12588286812106, 15750377512503, 5958838302789, 740984754242, 31725663621, 0, 0] := by
  rw [show A10K2.u5480 = KTree.node A10K2.u5476 (nat_lit 89310960) (nat_lit 858117379) (nat_lit 0) A10K2.u5479 from rfl, totK_node, atot5476, atot5479]
  decide +kernel

theorem arows5488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5488 = true := by
  rw [show A10K2.u5488 = KTree.node A10K2.u5484 (nat_lit 89467157) (nat_lit 7017242868) (nat_lit 0) A10K2.u5487 from rfl, allE_node, arows5484, irow5488, arows5487]
  all_goals rfl

theorem atot5488 : totK PA10K2 A10K2.u5488 = [0, 0, 2383604433247, 10747719822512, 15833137503608, 7989108958747, 1181501495173, 43254242352, 0, 0] := by
  rw [show A10K2.u5488 = KTree.node A10K2.u5484 (nat_lit 89467157) (nat_lit 7017242868) (nat_lit 0) A10K2.u5487 from rfl, totK_node, atot5484, atot5487]
  decide +kernel

theorem arows5495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5495 = true := by
  rw [show A10K2.u5495 = KTree.node A10K2.u5491 (nat_lit 89525320) (nat_lit 13706594045) (nat_lit 0) A10K2.u5494 from rfl, allE_node, arows5491, irow5495, arows5494]
  all_goals rfl

theorem atot5495 : totK PA10K2 A10K2.u5495 = [0, 0, 1970765185343, 9687985644134, 15912081270668, 9181594253371, 1558155682817, 74395553211, 0, 0] := by
  rw [show A10K2.u5495 = KTree.node A10K2.u5491 (nat_lit 89525320) (nat_lit 13706594045) (nat_lit 0) A10K2.u5494 from rfl, totK_node, atot5491, atot5494]
  decide +kernel

theorem arows5506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5506 = true := by
  rw [show A10K2.u5506 = KTree.node A10K2.u5502 (nat_lit 89558049) (nat_lit 10159752938) (nat_lit 0) A10K2.u5505 from rfl, allE_node, arows5502, irow5506, arows5505]
  all_goals rfl

theorem atot5506 : totK PA10K2 A10K2.u5506 = [0, 0, 836002267270, 6130697503544, 14336494770719, 12145166974217, 3451048834232, 293422010344, 0, 0] := by
  rw [show A10K2.u5506 = KTree.node A10K2.u5502 (nat_lit 89558049) (nat_lit 10159752938) (nat_lit 0) A10K2.u5505 from rfl, totK_node, atot5502, atot5505]
  decide +kernel

theorem arows5513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5513 = true := by
  rw [show A10K2.u5513 = KTree.node A10K2.u5509 (nat_lit 89737491) (nat_lit 10519385241) (nat_lit 0) A10K2.u5512 from rfl, allE_node, arows5509, irow5513, arows5512]
  all_goals rfl

theorem atot5513 : totK PA10K2 A10K2.u5513 = [0, 2211027775591, 10312976485822, 16115092142885, 9111475442781, 1501483309613, 170560783402, 91540553519, 6354482628, 0] := by
  rw [show A10K2.u5513 = KTree.node A10K2.u5509 (nat_lit 89737491) (nat_lit 10519385241) (nat_lit 0) A10K2.u5512 from rfl, totK_node, atot5509, atot5512]
  decide +kernel

theorem arows5521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5521 = true := by
  rw [show A10K2.u5521 = KTree.node A10K2.u5517 (nat_lit 89770130) (nat_lit 15235736758) (nat_lit 0) A10K2.u5520 from rfl, allE_node, arows5517, irow5521, arows5520]
  all_goals rfl

theorem atot5521 : totK PA10K2 A10K2.u5521 = [0, 593238721492, 4385111674183, 12045198551215, 14472541640596, 6654471008281, 959006322303, 37204059898, 0, 0] := by
  rw [show A10K2.u5521 = KTree.node A10K2.u5517 (nat_lit 89770130) (nat_lit 15235736758) (nat_lit 0) A10K2.u5520 from rfl, totK_node, atot5517, atot5520]
  decide +kernel

theorem arows5528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5528 = true := by
  rw [show A10K2.u5528 = KTree.node A10K2.u5524 (nat_lit 89874846) (nat_lit 15558691728) (nat_lit 0) A10K2.u5527 from rfl, allE_node, arows5524, irow5528, arows5527]
  all_goals rfl

theorem atot5528 : totK PA10K2 A10K2.u5528 = [0, 1652238446546, 8783183344751, 15931005968557, 10993508205964, 2433949251501, 121413703056, 0, 0, 0] := by
  rw [show A10K2.u5528 = KTree.node A10K2.u5524 (nat_lit 89874846) (nat_lit 15558691728) (nat_lit 0) A10K2.u5527 from rfl, totK_node, atot5524, atot5527]
  decide +kernel

theorem arows5537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5537 = true := by
  rw [show A10K2.u5537 = KTree.node A10K2.u5533 (nat_lit 89907263) (nat_lit 13987994865) (nat_lit 0) A10K2.u5536 from rfl, allE_node, arows5533, irow5537, arows5536]
  all_goals rfl

theorem atot5537 : totK PA10K2 A10K2.u5537 = [0, 0, 2085649707208, 10124721881948, 16256414860634, 9488918475769, 1666917415835, 75062079822, 0, 0] := by
  rw [show A10K2.u5537 = KTree.node A10K2.u5533 (nat_lit 89907263) (nat_lit 13987994865) (nat_lit 0) A10K2.u5536 from rfl, totK_node, atot5533, atot5536]
  decide +kernel

theorem arows5544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5544 = true := by
  rw [show A10K2.u5544 = KTree.node A10K2.u5540 (nat_lit 90003642) (nat_lit 14088912522) (nat_lit 0) A10K2.u5543 from rfl, allE_node, arows5540, irow5544, arows5543]
  all_goals rfl

theorem atot5544 : totK PA10K2 A10K2.u5544 = [0, 0, 1894365952470, 9450241467326, 15994264627235, 10074588239710, 1998304916167, 100968054516, 0, 0] := by
  rw [show A10K2.u5544 = KTree.node A10K2.u5540 (nat_lit 90003642) (nat_lit 14088912522) (nat_lit 0) A10K2.u5543 from rfl, totK_node, atot5540, atot5543]
  decide +kernel

theorem arows5552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5552 = true := by
  rw [show A10K2.u5552 = KTree.node A10K2.u5548 (nat_lit 90042003) (nat_lit 10748451029) (nat_lit 0) A10K2.u5551 from rfl, allE_node, arows5548, irow5552, arows5551]
  all_goals rfl

theorem atot5552 : totK PA10K2 A10K2.u5552 = [0, 0, 1376633234433, 7713326944616, 14992951963536, 11816242325130, 3556832995349, 366517233615, 7151180950, 0] := by
  rw [show A10K2.u5552 = KTree.node A10K2.u5548 (nat_lit 90042003) (nat_lit 10748451029) (nat_lit 0) A10K2.u5551 from rfl, totK_node, atot5548, atot5551]
  decide +kernel

theorem arows5559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5559 = true := by
  rw [show A10K2.u5559 = KTree.node A10K2.u5555 (nat_lit 90144134) (nat_lit 16058976194) (nat_lit 0) A10K2.u5558 from rfl, allE_node, arows5555, irow5559, arows5558]
  all_goals rfl

theorem atot5559 : totK PA10K2 A10K2.u5559 = [0, 1137674346764, 5677366893933, 11408365945298, 12343396274205, 7132865409022, 1475869027507, 75052822958, 0, 0] := by
  rw [show A10K2.u5559 = KTree.node A10K2.u5555 (nat_lit 90144134) (nat_lit 16058976194) (nat_lit 0) A10K2.u5558 from rfl, totK_node, atot5555, atot5558]
  decide +kernel

theorem arows5569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5569 = true := by
  rw [show A10K2.u5569 = KTree.node A10K2.u5565 (nat_lit 92304769) (nat_lit 8837345460) (nat_lit 0) A10K2.u5568 from rfl, allE_node, arows5565, irow5569, arows5568]
  all_goals rfl

theorem atot5569 : totK PA10K2 A10K2.u5569 = [0, 1080968927244, 6627707066510, 13891376425396, 11901425274771, 4266683464124, 630018329071, 30650496230, 0, 0] := by
  rw [show A10K2.u5569 = KTree.node A10K2.u5565 (nat_lit 92304769) (nat_lit 8837345460) (nat_lit 0) A10K2.u5568 from rfl, totK_node, atot5565, atot5568]
  decide +kernel

theorem arows5576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5576 = true := by
  rw [show A10K2.u5576 = KTree.node A10K2.u5572 (nat_lit 92407817) (nat_lit 9791040699) (nat_lit 0) A10K2.u5575 from rfl, allE_node, arows5572, irow5576, arows5575]
  all_goals rfl

theorem atot5576 : totK PA10K2 A10K2.u5576 = [0, 1337222637312, 7064382947454, 13923300858282, 11910148453301, 3777026276196, 344291964050, 5546304973, 0, 0] := by
  rw [show A10K2.u5576 = KTree.node A10K2.u5572 (nat_lit 92407817) (nat_lit 9791040699) (nat_lit 0) A10K2.u5575 from rfl, totK_node, atot5572, atot5575]
  decide +kernel

theorem arows5584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5584 = true := by
  rw [show A10K2.u5584 = KTree.node A10K2.u5580 (nat_lit 92440741) (nat_lit 7321820484) (nat_lit 0) A10K2.u5583 from rfl, allE_node, arows5580, irow5584, arows5583]
  all_goals rfl

theorem atot5584 : totK PA10K2 A10K2.u5584 = [0, 820244515340, 6158323339323, 14726494786003, 12802158252355, 3220982380444, 192413767994, 0, 0, 0] := by
  rw [show A10K2.u5584 = KTree.node A10K2.u5580 (nat_lit 92440741) (nat_lit 7321820484) (nat_lit 0) A10K2.u5583 from rfl, totK_node, atot5580, atot5583]
  decide +kernel

theorem arows5591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5591 = true := by
  rw [show A10K2.u5591 = KTree.node A10K2.u5587 (nat_lit 92499014) (nat_lit 15221459860) (nat_lit 0) A10K2.u5590 from rfl, allE_node, arows5587, irow5591, arows5590]
  all_goals rfl

theorem atot5591 : totK PA10K2 A10K2.u5591 = [0, 1364381863375, 7127865552039, 13848907112459, 12068700720507, 4428944714746, 566932322820, 13259410892, 0, 0] := by
  rw [show A10K2.u5591 = KTree.node A10K2.u5587 (nat_lit 92499014) (nat_lit 15221459860) (nat_lit 0) A10K2.u5590 from rfl, totK_node, atot5587, atot5590]
  decide +kernel

theorem arows5600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5600 = true := by
  rw [show A10K2.u5600 = KTree.node A10K2.u5596 (nat_lit 92541320) (nat_lit 14332909434) (nat_lit 0) A10K2.u5599 from rfl, allE_node, arows5596, irow5600, arows5599]
  all_goals rfl

theorem atot5600 : totK PA10K2 A10K2.u5600 = [0, 0, 2475548932779, 10981351208727, 15897580756548, 7890446245379, 1132798556476, 42603652279, 0, 0] := by
  rw [show A10K2.u5600 = KTree.node A10K2.u5596 (nat_lit 92541320) (nat_lit 14332909434) (nat_lit 0) A10K2.u5599 from rfl, totK_node, atot5596, atot5599]
  decide +kernel

theorem arows5607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5607 = true := by
  rw [show A10K2.u5607 = KTree.node A10K2.u5603 (nat_lit 92575906) (nat_lit 9793759839) (nat_lit 0) A10K2.u5606 from rfl, allE_node, arows5603, irow5607, arows5606]
  all_goals rfl

theorem atot5607 : totK PA10K2 A10K2.u5607 = [0, 0, 636622433169, 4985731899485, 13202650801409, 13552426114789, 5029376136396, 716451492200, 36134558889, 0] := by
  rw [show A10K2.u5607 = KTree.node A10K2.u5603 (nat_lit 92575906) (nat_lit 9793759839) (nat_lit 0) A10K2.u5606 from rfl, totK_node, atot5603, atot5606]
  decide +kernel

theorem arows5615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5615 = true := by
  rw [show A10K2.u5615 = KTree.node A10K2.u5611 (nat_lit 92682311) (nat_lit 5606879570) (nat_lit 0) A10K2.u5614 from rfl, allE_node, arows5611, irow5615, arows5614]
  all_goals rfl

theorem atot5615 : totK PA10K2 A10K2.u5615 = [0, 0, 1851767380580, 9689634444357, 16010996713550, 8759505847807, 1433591441640, 68853645116, 0, 0] := by
  rw [show A10K2.u5615 = KTree.node A10K2.u5611 (nat_lit 92682311) (nat_lit 5606879570) (nat_lit 0) A10K2.u5614 from rfl, totK_node, atot5611, atot5614]
  decide +kernel

theorem arows5622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5622 = true := by
  rw [show A10K2.u5622 = KTree.node A10K2.u5618 (nat_lit 92733446) (nat_lit 14882822736) (nat_lit 0) A10K2.u5621 from rfl, allE_node, arows5618, irow5622, arows5621]
  all_goals rfl

theorem atot5622 : totK PA10K2 A10K2.u5622 = [0, 0, 1360263751570, 7603693205709, 14978577653453, 11284916982981, 2857719625571, 262143700550, 5676195732, 0] := by
  rw [show A10K2.u5622 = KTree.node A10K2.u5618 (nat_lit 92733446) (nat_lit 14882822736) (nat_lit 0) A10K2.u5621 from rfl, totK_node, atot5618, atot5621]
  decide +kernel

theorem arows5635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5635 = true := by
  rw [show A10K2.u5635 = KTree.node A10K2.u5631 (nat_lit 92881409) (nat_lit 10410430643) (nat_lit 0) A10K2.u5634 from rfl, allE_node, arows5631, irow5635, arows5634]
  all_goals rfl

theorem atot5635 : totK PA10K2 A10K2.u5635 = [0, 2224879412960, 10051946618559, 15131936674126, 8902001530801, 2343918725126, 286572112451, 6853348008, 0, 0] := by
  rw [show A10K2.u5635 = KTree.node A10K2.u5631 (nat_lit 92881409) (nat_lit 10410430643) (nat_lit 0) A10K2.u5634 from rfl, totK_node, atot5631, atot5634]
  decide +kernel

theorem arows5642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5642 = true := by
  rw [show A10K2.u5642 = KTree.node A10K2.u5638 (nat_lit 92913737) (nat_lit 9577026704) (nat_lit 0) A10K2.u5641 from rfl, allE_node, arows5638, irow5642, arows5641]
  all_goals rfl

theorem atot5642 : totK PA10K2 A10K2.u5642 = [0, 273815470041, 3217821066400, 11486528018402, 15438095599343, 7034229878677, 957319584879, 37204059898, 0, 0] := by
  rw [show A10K2.u5642 = KTree.node A10K2.u5638 (nat_lit 92913737) (nat_lit 9577026704) (nat_lit 0) A10K2.u5641 from rfl, totK_node, atot5638, atot5641]
  decide +kernel

theorem arows5650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5650 = true := by
  rw [show A10K2.u5650 = KTree.node A10K2.u5646 (nat_lit 92944229) (nat_lit 6911264788) (nat_lit 0) A10K2.u5649 from rfl, allE_node, arows5646, irow5650, arows5649]
  all_goals rfl

theorem atot5650 : totK PA10K2 A10K2.u5650 = [0, 1884919740252, 9583482196943, 15801638586301, 9181442614769, 1652716014894, 83929645986, 0, 0, 0] := by
  rw [show A10K2.u5650 = KTree.node A10K2.u5646 (nat_lit 92944229) (nat_lit 6911264788) (nat_lit 0) A10K2.u5649 from rfl, totK_node, atot5646, atot5649]
  decide +kernel

theorem arows5657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5657 = true := by
  rw [show A10K2.u5657 = KTree.node A10K2.u5653 (nat_lit 92983578) (nat_lit 11511869346) (nat_lit 0) A10K2.u5656 from rfl, allE_node, arows5653, irow5657, arows5656]
  all_goals rfl

theorem atot5657 : totK PA10K2 A10K2.u5657 = [0, 1061690136320, 6178399797591, 13840530921200, 13095856612500, 4054177926246, 404145265705, 6354482628, 0, 0] := by
  rw [show A10K2.u5657 = KTree.node A10K2.u5653 (nat_lit 92983578) (nat_lit 11511869346) (nat_lit 0) A10K2.u5656 from rfl, totK_node, atot5653, atot5656]
  decide +kernel

theorem arows5666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5666 = true := by
  rw [show A10K2.u5666 = KTree.node A10K2.u5662 (nat_lit 93042977) (nat_lit 8297158483) (nat_lit 0) A10K2.u5665 from rfl, allE_node, arows5662, irow5666, arows5665]
  all_goals rfl

theorem atot5666 : totK PA10K2 A10K2.u5666 = [0, 307923820525, 4296436572621, 13424353329935, 15110464118095, 6134377119223, 676605699075, 13204174009, 0, 0] := by
  rw [show A10K2.u5666 = KTree.node A10K2.u5662 (nat_lit 93042977) (nat_lit 8297158483) (nat_lit 0) A10K2.u5665 from rfl, totK_node, atot5662, atot5665]
  decide +kernel

theorem arows5673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5673 = true := by
  rw [show A10K2.u5673 = KTree.node A10K2.u5669 (nat_lit 93150056) (nat_lit 7737754118) (nat_lit 0) A10K2.u5672 from rfl, allE_node, arows5669, irow5673, arows5672]
  all_goals rfl

theorem atot5673 : totK PA10K2 A10K2.u5673 = [0, 0, 1374790201675, 8111338834577, 15809063707661, 11020541862738, 2295622780576, 118446377288, 0, 0] := by
  rw [show A10K2.u5673 = KTree.node A10K2.u5669 (nat_lit 93150056) (nat_lit 7737754118) (nat_lit 0) A10K2.u5672 from rfl, totK_node, atot5669, atot5672]
  decide +kernel

theorem arows5681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5681 = true := by
  rw [show A10K2.u5681 = KTree.node A10K2.u5677 (nat_lit 93187464) (nat_lit 11030394722) (nat_lit 0) A10K2.u5680 from rfl, allE_node, arows5677, irow5681, arows5680]
  all_goals rfl

theorem atot5681 : totK PA10K2 A10K2.u5681 = [0, 0, 1337977996624, 7085751710722, 13447789405344, 11151369018306, 4197788503556, 677103514254, 36704093874, 0] := by
  rw [show A10K2.u5681 = KTree.node A10K2.u5677 (nat_lit 93187464) (nat_lit 11030394722) (nat_lit 0) A10K2.u5680 from rfl, totK_node, atot5677, atot5680]
  decide +kernel

theorem arows5688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5688 = true := by
  rw [show A10K2.u5688 = KTree.node A10K2.u5684 (nat_lit 93225534) (nat_lit 7718677822) (nat_lit 128) A10K2.u5687 from rfl, allE_node, arows5684, irow5688, arows5687]
  all_goals rfl

theorem atot5688 : totK PA10K2 A10K2.u5688 = [0, 0, 820027295343, 6409954441528, 15299898331551, 12341306385012, 2569449913771, 117488367958, 0, 0] := by
  rw [show A10K2.u5688 = KTree.node A10K2.u5684 (nat_lit 93225534) (nat_lit 7718677822) (nat_lit 128) A10K2.u5687 from rfl, totK_node, atot5684, atot5687]
  decide +kernel

theorem arows5698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5698 = true := by
  rw [show A10K2.u5698 = KTree.node A10K2.u5694 (nat_lit 93285490) (nat_lit 11846839113) (nat_lit 0) A10K2.u5697 from rfl, allE_node, arows5694, irow5698, arows5697]
  all_goals rfl

theorem atot5698 : totK PA10K2 A10K2.u5698 = [0, 800527158634, 4854005974796, 11362498612692, 12761082904109, 7158517833345, 1887800221780, 229258428111, 6239673734, 0] := by
  rw [show A10K2.u5698 = KTree.node A10K2.u5694 (nat_lit 93285490) (nat_lit 11846839113) (nat_lit 0) A10K2.u5697 from rfl, totK_node, atot5694, atot5697]
  decide +kernel

theorem arows5705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5705 = true := by
  rw [show A10K2.u5705 = KTree.node A10K2.u5701 (nat_lit 93351877) (nat_lit 2639526079) (nat_lit 0) A10K2.u5704 from rfl, allE_node, arows5701, irow5705, arows5704]
  all_goals rfl

theorem atot5705 : totK PA10K2 A10K2.u5705 = [0, 1244898366231, 6960455566659, 13719783016906, 11484993810160, 3989063242394, 553418289026, 30650496230, 0, 0] := by
  rw [show A10K2.u5705 = KTree.node A10K2.u5701 (nat_lit 93351877) (nat_lit 2639526079) (nat_lit 0) A10K2.u5704 from rfl, totK_node, atot5701, atot5704]
  decide +kernel

theorem arows5713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5713 = true := by
  rw [show A10K2.u5713 = KTree.node A10K2.u5709 (nat_lit 93399218) (nat_lit 15135211413) (nat_lit 0) A10K2.u5712 from rfl, allE_node, arows5709, irow5713, arows5712]
  all_goals rfl

theorem atot5713 : totK PA10K2 A10K2.u5713 = [0, 1590835445191, 7798413622917, 14079441137846, 11155630942296, 3307833679186, 295201086317, 5546304973, 0, 0] := by
  rw [show A10K2.u5713 = KTree.node A10K2.u5709 (nat_lit 93399218) (nat_lit 15135211413) (nat_lit 0) A10K2.u5712 from rfl, totK_node, atot5709, atot5712]
  decide +kernel

theorem arows5720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5720 = true := by
  rw [show A10K2.u5720 = KTree.node A10K2.u5716 (nat_lit 93433044) (nat_lit 10735820018) (nat_lit 0) A10K2.u5719 from rfl, allE_node, arows5716, irow5720, arows5719]
  all_goals rfl

theorem atot5720 : totK PA10K2 A10K2.u5720 = [0, 461607179050, 4387937229647, 12899831526379, 14280502504663, 5499734388018, 674206905859, 31082886609, 0, 0] := by
  rw [show A10K2.u5720 = KTree.node A10K2.u5716 (nat_lit 93433044) (nat_lit 10735820018) (nat_lit 0) A10K2.u5719 from rfl, totK_node, atot5716, atot5719]
  decide +kernel

theorem arows5729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5729 = true := by
  rw [show A10K2.u5729 = KTree.node A10K2.u5725 (nat_lit 93461952) (nat_lit 15038608404) (nat_lit 0) A10K2.u5728 from rfl, allE_node, arows5725, irow5729, arows5728]
  all_goals rfl

theorem atot5729 : totK PA10K2 A10K2.u5729 = [0, 2032779298570, 9333254746106, 14702405218593, 9384572799762, 2466670677281, 243222495927, 6121173289, 0, 0] := by
  rw [show A10K2.u5729 = KTree.node A10K2.u5725 (nat_lit 93461952) (nat_lit 15038608404) (nat_lit 0) A10K2.u5728 from rfl, totK_node, atot5725, atot5728]
  decide +kernel

theorem arows5736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5736 = true := by
  rw [show A10K2.u5736 = KTree.node A10K2.u5732 (nat_lit 93497569) (nat_lit 4901734374) (nat_lit 0) A10K2.u5735 from rfl, allE_node, arows5732, irow5736, arows5735]
  all_goals rfl

theorem atot5736 : totK PA10K2 A10K2.u5736 = [0, 311053418201, 4623241086845, 13999170655476, 14210175450674, 4362525651873, 420798226595, 6354482628, 0, 0] := by
  rw [show A10K2.u5736 = KTree.node A10K2.u5732 (nat_lit 93497569) (nat_lit 4901734374) (nat_lit 0) A10K2.u5735 from rfl, totK_node, atot5732, atot5735]
  decide +kernel

theorem arows5744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5744 = true := by
  rw [show A10K2.u5744 = KTree.node A10K2.u5740 (nat_lit 93605888) (nat_lit 15638348816) (nat_lit 0) A10K2.u5743 from rfl, allE_node, arows5740, irow5744, arows5743]
  all_goals rfl

theorem atot5744 : totK PA10K2 A10K2.u5744 = [0, 0, 2497145563883, 10924122967802, 15751728512326, 7705043151149, 1079474177899, 44026197503, 0, 0] := by
  rw [show A10K2.u5744 = KTree.node A10K2.u5740 (nat_lit 93605888) (nat_lit 15638348816) (nat_lit 0) A10K2.u5743 from rfl, totK_node, atot5740, atot5743]
  decide +kernel

theorem arows5751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5751 = true := by
  rw [show A10K2.u5751 = KTree.node A10K2.u5747 (nat_lit 93673706) (nat_lit 11630642758) (nat_lit 0) A10K2.u5750 from rfl, allE_node, arows5747, irow5751, arows5750]
  all_goals rfl

theorem atot5751 : totK PA10K2 A10K2.u5751 = [0, 0, 2026781252217, 9972412220671, 15927403425497, 8657656310488, 1365551219005, 69384189482, 0, 0] := by
  rw [show A10K2.u5751 = KTree.node A10K2.u5747 (nat_lit 93673706) (nat_lit 11630642758) (nat_lit 0) A10K2.u5750 from rfl, totK_node, atot5747, atot5750]
  decide +kernel

theorem arows5762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5762 = true := by
  rw [show A10K2.u5762 = KTree.node A10K2.u5758 (nat_lit 93733765) (nat_lit 5148725130) (nat_lit 0) A10K2.u5761 from rfl, allE_node, arows5758, irow5762, arows5761]
  all_goals rfl

theorem atot5762 : totK PA10K2 A10K2.u5762 = [0, 0, 1596932877270, 8866947223690, 15928373433497, 9497750863450, 1613973509316, 74011771552, 0, 0] := by
  rw [show A10K2.u5762 = KTree.node A10K2.u5758 (nat_lit 93733765) (nat_lit 5148725130) (nat_lit 0) A10K2.u5761 from rfl, totK_node, atot5758, atot5761]
  decide +kernel

theorem arows5769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5769 = true := by
  rw [show A10K2.u5769 = KTree.node A10K2.u5765 (nat_lit 94372385) (nat_lit 10183229173) (nat_lit 0) A10K2.u5768 from rfl, allE_node, arows5765, irow5769, arows5768]
  all_goals rfl

theorem atot5769 : totK PA10K2 A10K2.u5769 = [0, 0, 1549638306074, 7451552155178, 13739002449170, 10960909500649, 3338538805215, 378246403776, 6354482628, 0] := by
  rw [show A10K2.u5769 = KTree.node A10K2.u5765 (nat_lit 94372385) (nat_lit 10183229173) (nat_lit 0) A10K2.u5768 from rfl, totK_node, atot5765, atot5768]
  decide +kernel

theorem arows5777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5777 = true := by
  rw [show A10K2.u5777 = KTree.node A10K2.u5773 (nat_lit 94405104) (nat_lit 14112702326) (nat_lit 0) A10K2.u5776 from rfl, allE_node, arows5773, irow5777, arows5776]
  all_goals rfl

theorem atot5777 : totK PA10K2 A10K2.u5777 = [0, 0, 652692863706, 5689442892133, 14299712193300, 13096192246868, 4124542131810, 533726275724, 30650496230, 0] := by
  rw [show A10K2.u5777 = KTree.node A10K2.u5773 (nat_lit 94405104) (nat_lit 14112702326) (nat_lit 0) A10K2.u5776 from rfl, totK_node, atot5773, atot5776]
  decide +kernel

theorem arows5784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5784 = true := by
  rw [show A10K2.u5784 = KTree.node A10K2.u5780 (nat_lit 94509154) (nat_lit 8364527193) (nat_lit 0) A10K2.u5783 from rfl, allE_node, arows5780, irow5784, arows5783]
  all_goals rfl

theorem atot5784 : totK PA10K2 A10K2.u5784 = [0, 0, 2027102209138, 9002931572110, 14370368549835, 9715039544528, 2589595986598, 264356973019, 5546304973, 0] := by
  rw [show A10K2.u5784 = KTree.node A10K2.u5780 (nat_lit 94509154) (nat_lit 8364527193) (nat_lit 0) A10K2.u5783 from rfl, totK_node, atot5780, atot5783]
  decide +kernel

theorem arows5793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5793 = true := by
  rw [show A10K2.u5793 = KTree.node A10K2.u5789 (nat_lit 94546701) (nat_lit 5814114857) (nat_lit 0) A10K2.u5792 from rfl, allE_node, arows5789, irow5793, arows5792]
  all_goals rfl

theorem atot5793 : totK PA10K2 A10K2.u5793 = [0, 0, 882797691073, 6120464480811, 14020897091195, 12549831772189, 3749045965855, 393214209434, 6354482628, 0] := by
  rw [show A10K2.u5793 = KTree.node A10K2.u5789 (nat_lit 94546701) (nat_lit 5814114857) (nat_lit 0) A10K2.u5792 from rfl, totK_node, atot5789, atot5792]
  decide +kernel

theorem arows5800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5800 = true := by
  rw [show A10K2.u5800 = KTree.node A10K2.u5796 (nat_lit 94971546) (nat_lit 15159780562) (nat_lit 0) A10K2.u5799 from rfl, allE_node, arows5796, irow5800, arows5799]
  all_goals rfl

theorem atot5800 : totK PA10K2 A10K2.u5800 = [0, 0, 2090619146978, 9956462373322, 16071006215486, 9297013723725, 1592733887368, 69432964872, 0, 0] := by
  rw [show A10K2.u5800 = KTree.node A10K2.u5796 (nat_lit 94971546) (nat_lit 15159780562) (nat_lit 0) A10K2.u5799 from rfl, totK_node, atot5796, atot5799]
  decide +kernel

theorem arows5808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5808 = true := by
  rw [show A10K2.u5808 = KTree.node A10K2.u5804 (nat_lit 95004094) (nat_lit 16085329573) (nat_lit 0) A10K2.u5807 from rfl, allE_node, arows5804, irow5808, arows5807]
  all_goals rfl

theorem atot5808 : totK PA10K2 A10K2.u5808 = [0, 0, 724045030467, 5815769827755, 14392522940384, 13066515657575, 4179792180726, 545555451182, 31082886609, 0] := by
  rw [show A10K2.u5808 = KTree.node A10K2.u5804 (nat_lit 95004094) (nat_lit 16085329573) (nat_lit 0) A10K2.u5807 from rfl, totK_node, atot5804, atot5807]
  decide +kernel

theorem arows5815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5815 = true := by
  rw [show A10K2.u5815 = KTree.node A10K2.u5811 (nat_lit 95036701) (nat_lit 6342138324) (nat_lit 0) A10K2.u5814 from rfl, allE_node, arows5811, irow5815, arows5814]
  all_goals rfl

theorem atot5815 : totK PA10K2 A10K2.u5815 = [0, 0, 2033205975319, 9021672748366, 14292218573852, 9790083058791, 2677101316460, 272145526173, 6121173289, 0] := by
  rw [show A10K2.u5815 = KTree.node A10K2.u5811 (nat_lit 95036701) (nat_lit 6342138324) (nat_lit 0) A10K2.u5814 from rfl, totK_node, atot5811, atot5814]
  decide +kernel

theorem arows5825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5825 = true := by
  rw [show A10K2.u5825 = KTree.node A10K2.u5821 (nat_lit 95071926) (nat_lit 16237930875) (nat_lit 0) A10K2.u5824 from rfl, allE_node, arows5821, irow5825, arows5824]
  all_goals rfl

theorem atot5825 : totK PA10K2 A10K2.u5825 = [0, 0, 886000797908, 6143747090150, 14083495147720, 12580727776724, 3753623772051, 393297678592, 6354482628, 0] := by
  rw [show A10K2.u5825 = KTree.node A10K2.u5821 (nat_lit 95071926) (nat_lit 16237930875) (nat_lit 0) A10K2.u5824 from rfl, totK_node, atot5821, atot5824]
  decide +kernel

theorem arows5832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5832 = true := by
  rw [show A10K2.u5832 = KTree.node A10K2.u5828 (nat_lit 95420928) (nat_lit 15717770038) (nat_lit 0) A10K2.u5831 from rfl, allE_node, arows5828, irow5832, arows5831]
  all_goals rfl

theorem atot5832 : totK PA10K2 A10K2.u5832 = [0, 0, 2172540182764, 10178867290856, 15977059179556, 9112380073594, 1527043236123, 69316649749, 0, 0] := by
  rw [show A10K2.u5832 = KTree.node A10K2.u5828 (nat_lit 95420928) (nat_lit 15717770038) (nat_lit 0) A10K2.u5831 from rfl, totK_node, atot5828, atot5831]
  decide +kernel

theorem arows5840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5840 = true := by
  rw [show A10K2.u5840 = KTree.node A10K2.u5836 (nat_lit 95456727) (nat_lit 5736047064) (nat_lit 128) A10K2.u5839 from rfl, allE_node, arows5836, irow5840, arows5839]
  all_goals rfl

theorem atot5840 : totK PA10K2 A10K2.u5840 = [0, 0, 458520426296, 4679474594261, 13153296838698, 13553897506034, 4912185641661, 717104386475, 35767183343, 0] := by
  rw [show A10K2.u5840 = KTree.node A10K2.u5836 (nat_lit 95456727) (nat_lit 5736047064) (nat_lit 128) A10K2.u5839 from rfl, totK_node, atot5836, atot5839]
  decide +kernel

theorem arows5847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5847 = true := by
  rw [show A10K2.u5847 = KTree.node A10K2.u5843 (nat_lit 95503575) (nat_lit 12041950585) (nat_lit 0) A10K2.u5846 from rfl, allE_node, arows5843, irow5847, arows5846]
  all_goals rfl

theorem atot5847 : totK PA10K2 A10K2.u5847 = [0, 0, 2042805508435, 9849298866092, 15880311158635, 9133882848017, 1454380981801, 69845597466, 0, 0] := by
  rw [show A10K2.u5847 = KTree.node A10K2.u5843 (nat_lit 95503575) (nat_lit 12041950585) (nat_lit 0) A10K2.u5846 from rfl, totK_node, atot5843, atot5846]
  decide +kernel

theorem arows5856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5856 = true := by
  rw [show A10K2.u5856 = KTree.node A10K2.u5852 (nat_lit 95540408) (nat_lit 3849125097) (nat_lit 0) A10K2.u5855 from rfl, allE_node, arows5852, irow5856, arows5855]
  all_goals rfl

theorem atot5856 : totK PA10K2 A10K2.u5856 = [0, 0, 733026072910, 4931958482005, 12595500420314, 13341892909696, 5093423464270, 760698487588, 36768997705, 0] := by
  rw [show A10K2.u5856 = KTree.node A10K2.u5852 (nat_lit 95540408) (nat_lit 3849125097) (nat_lit 0) A10K2.u5855 from rfl, totK_node, atot5852, atot5855]
  decide +kernel

theorem arows5863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5863 = true := by
  rw [show A10K2.u5863 = KTree.node A10K2.u5859 (nat_lit 95569682) (nat_lit 14982456772) (nat_lit 0) A10K2.u5862 from rfl, allE_node, arows5859, irow5863, arows5862]
  all_goals rfl

theorem atot5863 : totK PA10K2 A10K2.u5863 = [0, 0, 1584630885100, 8609813516038, 15328847378117, 10039973911395, 1997507570181, 108052190153, 0, 0] := by
  rw [show A10K2.u5863 = KTree.node A10K2.u5859 (nat_lit 95569682) (nat_lit 14982456772) (nat_lit 0) A10K2.u5862 from rfl, totK_node, atot5859, atot5862]
  decide +kernel

theorem arows5871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5871 = true := by
  rw [show A10K2.u5871 = KTree.node A10K2.u5867 (nat_lit 95683364) (nat_lit 13711877624) (nat_lit 0) A10K2.u5870 from rfl, allE_node, arows5867, irow5871, arows5870]
  all_goals rfl

theorem atot5871 : totK PA10K2 A10K2.u5871 = [0, 0, 0, 2746544276041, 11890823628279, 15651093216869, 6289902084689, 893261930448, 36743231635, 0] := by
  rw [show A10K2.u5871 = KTree.node A10K2.u5867 (nat_lit 95683364) (nat_lit 13711877624) (nat_lit 0) A10K2.u5870 from rfl, totK_node, atot5867, atot5870]
  decide +kernel

theorem arows5878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5878 = true := by
  rw [show A10K2.u5878 = KTree.node A10K2.u5874 (nat_lit 95763204) (nat_lit 12870166893) (nat_lit 0) A10K2.u5877 from rfl, allE_node, arows5874, irow5878, arows5877]
  all_goals rfl

theorem atot5878 : totK PA10K2 A10K2.u5878 = [0, 0, 0, 2780939419511, 11645200816727, 15402861669878, 6904441084794, 1116917134538, 43726476913, 0] := by
  rw [show A10K2.u5878 = KTree.node A10K2.u5874 (nat_lit 95763204) (nat_lit 12870166893) (nat_lit 0) A10K2.u5877 from rfl, totK_node, atot5874, atot5877]
  decide +kernel

theorem arows5890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5890 = true := by
  rw [show A10K2.u5890 = KTree.node A10K2.u5886 (nat_lit 95827799) (nat_lit 4629229145) (nat_lit 0) A10K2.u5889 from rfl, allE_node, arows5886, irow5890, arows5889]
  all_goals rfl

theorem atot5890 : totK PA10K2 A10K2.u5890 = [0, 0, 0, 2019087752847, 9821939421853, 15571720507128, 8202592485503, 1469351666759, 86885565800, 0] := by
  rw [show A10K2.u5890 = KTree.node A10K2.u5886 (nat_lit 95827799) (nat_lit 4629229145) (nat_lit 0) A10K2.u5889 from rfl, totK_node, atot5886, atot5889]
  decide +kernel

theorem arows5897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5897 = true := by
  rw [show A10K2.u5897 = KTree.node A10K2.u5893 (nat_lit 95868193) (nat_lit 8687529398) (nat_lit 0) A10K2.u5896 from rfl, allE_node, arows5893, irow5897, arows5896]
  all_goals rfl

theorem atot5897 : totK PA10K2 A10K2.u5897 = [1058637277771, 4454015480509, 6525423530273, 3602832728812, 2632564154972, 7480909203926, 8271499064152, 3022623391099, 359155326295, 6354482628] := by
  rw [show A10K2.u5897 = KTree.node A10K2.u5893 (nat_lit 95868193) (nat_lit 8687529398) (nat_lit 0) A10K2.u5896 from rfl, totK_node, atot5893, atot5896]
  decide +kernel

theorem arows5905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5905 = true := by
  rw [show A10K2.u5905 = KTree.node A10K2.u5901 (nat_lit 100692236) (nat_lit 11654116419) (nat_lit 0) A10K2.u5904 from rfl, allE_node, arows5901, irow5905, arows5904]
  all_goals rfl

theorem atot5905 : totK PA10K2 A10K2.u5905 = [1269857319490, 7295069364967, 14301125424767, 11528403979337, 3661198112825, 485167435405, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u5905 = KTree.node A10K2.u5901 (nat_lit 100692236) (nat_lit 11654116419) (nat_lit 0) A10K2.u5904 from rfl, totK_node, atot5901, atot5904]
  decide +kernel

theorem arows5912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5912 = true := by
  rw [show A10K2.u5912 = KTree.node A10K2.u5908 (nat_lit 100724187) (nat_lit 6412900983) (nat_lit 0) A10K2.u5911 from rfl, allE_node, arows5908, irow5912, arows5911]
  all_goals rfl

theorem atot5912 : totK PA10K2 A10K2.u5912 = [1047365728931, 6277136542576, 13481764011635, 12440621692263, 4506273470028, 503714638540, 10957026886, 0, 0, 0] := by
  rw [show A10K2.u5912 = KTree.node A10K2.u5908 (nat_lit 100724187) (nat_lit 6412900983) (nat_lit 0) A10K2.u5911 from rfl, totK_node, atot5908, atot5911]
  decide +kernel

theorem arows5921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5921 = true := by
  rw [show A10K2.u5921 = KTree.node A10K2.u5917 (nat_lit 100830220) (nat_lit 10337124524) (nat_lit 0) A10K2.u5920 from rfl, allE_node, arows5917, irow5921, arows5920]
  all_goals rfl

theorem atot5921 : totK PA10K2 A10K2.u5921 = [1081099675338, 6398009805582, 13930764309205, 12233617902608, 3701972674054, 373567152327, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5921 = KTree.node A10K2.u5917 (nat_lit 100830220) (nat_lit 10337124524) (nat_lit 0) A10K2.u5920 from rfl, totK_node, atot5917, atot5920]
  decide +kernel

theorem arows5928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5928 = true := by
  rw [show A10K2.u5928 = KTree.node A10K2.u5924 (nat_lit 100875678) (nat_lit 15612259748) (nat_lit 0) A10K2.u5927 from rfl, allE_node, arows5924, irow5928, arows5927]
  all_goals rfl

theorem atot5928 : totK PA10K2 A10K2.u5928 = [1829857935280, 9288407728719, 16051633263170, 10645365778881, 2314489294415, 133627430404, 0, 0, 0, 0] := by
  rw [show A10K2.u5928 = KTree.node A10K2.u5924 (nat_lit 100875678) (nat_lit 15612259748) (nat_lit 0) A10K2.u5927 from rfl, totK_node, atot5924, atot5927]
  decide +kernel

theorem arows5936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5936 = true := by
  rw [show A10K2.u5936 = KTree.node A10K2.u5932 (nat_lit 100917298) (nat_lit 10491640441) (nat_lit 0) A10K2.u5935 from rfl, allE_node, arows5932, irow5936, arows5935]
  all_goals rfl

theorem atot5936 : totK PA10K2 A10K2.u5936 = [0, 2283024458756, 10462780365530, 16199916139502, 9358216076696, 1691518764699, 75062079822, 0, 0, 0] := by
  rw [show A10K2.u5936 = KTree.node A10K2.u5932 (nat_lit 100917298) (nat_lit 10491640441) (nat_lit 0) A10K2.u5935 from rfl, totK_node, atot5932, atot5935]
  decide +kernel

theorem arows5943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5943 = true := by
  rw [show A10K2.u5943 = KTree.node A10K2.u5939 (nat_lit 100946039) (nat_lit 11087637177) (nat_lit 0) A10K2.u5942 from rfl, allE_node, arows5939, irow5943, arows5942]
  all_goals rfl

theorem atot5943 : totK PA10K2 A10K2.u5943 = [0, 1907709826213, 9681316665725, 15999904880969, 9181721971365, 1591041386839, 71567867718, 0, 0, 0] := by
  rw [show A10K2.u5943 = KTree.node A10K2.u5939 (nat_lit 100946039) (nat_lit 11087637177) (nat_lit 0) A10K2.u5942 from rfl, totK_node, atot5939, atot5942]
  decide +kernel

theorem arows5953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5953 = true := by
  rw [show A10K2.u5953 = KTree.node A10K2.u5949 (nat_lit 100977164) (nat_lit 11719777864) (nat_lit 0) A10K2.u5952 from rfl, allE_node, arows5949, irow5953, arows5952]
  all_goals rfl

theorem atot5953 : totK PA10K2 A10K2.u5953 = [0, 795232957208, 5001200499563, 12173733185009, 13320384266121, 5593403209710, 847302056601, 36134558889, 0, 0] := by
  rw [show A10K2.u5953 = KTree.node A10K2.u5949 (nat_lit 100977164) (nat_lit 11719777864) (nat_lit 0) A10K2.u5952 from rfl, totK_node, atot5949, atot5952]
  decide +kernel

theorem arows5960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5960 = true := by
  rw [show A10K2.u5960 = KTree.node A10K2.u5956 (nat_lit 101077284) (nat_lit 13966830622) (nat_lit 0) A10K2.u5959 from rfl, allE_node, arows5956, irow5960, arows5959]
  all_goals rfl

theorem atot5960 : totK PA10K2 A10K2.u5960 = [0, 993426424225, 7066831668446, 15342080365872, 11538079305440, 2445357330211, 118649193699, 0, 0, 0] := by
  rw [show A10K2.u5960 = KTree.node A10K2.u5956 (nat_lit 101077284) (nat_lit 13966830622) (nat_lit 0) A10K2.u5959 from rfl, totK_node, atot5956, atot5959]
  decide +kernel

theorem arows5968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5968 = true := by
  rw [show A10K2.u5968 = KTree.node A10K2.u5964 (nat_lit 101129690) (nat_lit 12717247733) (nat_lit 0) A10K2.u5967 from rfl, allE_node, arows5964, irow5968, arows5967]
  all_goals rfl

theorem atot5968 : totK PA10K2 A10K2.u5968 = [0, 2164142223959, 9624501646989, 15201213395592, 9854534674494, 2499816825551, 231607786777, 5676195732, 0, 0] := by
  rw [show A10K2.u5968 = KTree.node A10K2.u5964 (nat_lit 101129690) (nat_lit 12717247733) (nat_lit 0) A10K2.u5967 from rfl, totK_node, atot5964, atot5967]
  decide +kernel

theorem arows5975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5975 = true := by
  rw [show A10K2.u5975 = KTree.node A10K2.u5971 (nat_lit 101719073) (nat_lit 10086951556) (nat_lit 0) A10K2.u5974 from rfl, allE_node, arows5971, irow5975, arows5974]
  all_goals rfl

theorem atot5975 : totK PA10K2 A10K2.u5975 = [2182481654920, 9544924870299, 14182093954285, 8797348708940, 3307930746361, 796249606901, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u5975 = KTree.node A10K2.u5971 (nat_lit 101719073) (nat_lit 10086951556) (nat_lit 0) A10K2.u5974 from rfl, totK_node, atot5971, atot5974]
  decide +kernel

theorem arows5984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5984 = true := by
  rw [show A10K2.u5984 = KTree.node A10K2.u5980 (nat_lit 101751816) (nat_lit 14462297835) (nat_lit 0) A10K2.u5983 from rfl, allE_node, arows5980, irow5984, arows5983]
  all_goals rfl

theorem atot5984 : totK PA10K2 A10K2.u5984 = [152930188526, 3120511994844, 11913891041972, 15702253843724, 6833851056807, 938147498426, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u5984 = KTree.node A10K2.u5980 (nat_lit 101751816) (nat_lit 14462297835) (nat_lit 0) A10K2.u5983 from rfl, totK_node, atot5980, atot5983]
  decide +kernel

theorem arows5991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5991 = true := by
  rw [show A10K2.u5991 = KTree.node A10K2.u5987 (nat_lit 101856557) (nat_lit 6552860836) (nat_lit 0) A10K2.u5990 from rfl, allE_node, arows5987, irow5991, arows5990]
  all_goals rfl

theorem atot5991 : totK PA10K2 A10K2.u5991 = [1994620526462, 9896050886748, 15849271682787, 8899433830172, 1537679343636, 68954905367, 0, 0, 0, 0] := by
  rw [show A10K2.u5991 = KTree.node A10K2.u5987 (nat_lit 101856557) (nat_lit 6552860836) (nat_lit 0) A10K2.u5990 from rfl, totK_node, atot5987, atot5990]
  decide +kernel

theorem arows5999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5999 = true := by
  rw [show A10K2.u5999 = KTree.node A10K2.u5995 (nat_lit 101896260) (nat_lit 11552108224) (nat_lit 0) A10K2.u5998 from rfl, allE_node, arows5995, irow5999, arows5998]
  all_goals rfl

theorem atot5999 : totK PA10K2 A10K2.u5999 = [0, 2681404144140, 11672302006422, 15831511687917, 6843142720752, 963579794789, 37172849495, 0, 0, 0] := by
  rw [show A10K2.u5999 = KTree.node A10K2.u5995 (nat_lit 101896260) (nat_lit 11552108224) (nat_lit 0) A10K2.u5998 from rfl, totK_node, atot5995, atot5998]
  decide +kernel

theorem arows6006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6006 = true := by
  rw [show A10K2.u6006 = KTree.node A10K2.u6002 (nat_lit 102002945) (nat_lit 10385574571) (nat_lit 0) A10K2.u6005 from rfl, allE_node, arows6002, irow6006, arows6005]
  all_goals rfl

theorem atot6006 : totK PA10K2 A10K2.u6006 = [0, 2386303947850, 10736611369819, 16025286736554, 8242290589276, 1209789350831, 43282714182, 0, 0, 0] := by
  rw [show A10K2.u6006 = KTree.node A10K2.u6002 (nat_lit 102002945) (nat_lit 10385574571) (nat_lit 0) A10K2.u6005 from rfl, totK_node, atot6002, atot6005]
  decide +kernel

theorem arows6017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6017 = true := by
  rw [show A10K2.u6017 = KTree.node A10K2.u6013 (nat_lit 102127734) (nat_lit 8236973296) (nat_lit 0) A10K2.u6016 from rfl, allE_node, arows6013, irow6017, arows6016]
  all_goals rfl

theorem atot6017 : totK PA10K2 A10K2.u6017 = [0, 1101717613284, 7357140152091, 15314951483147, 11105934705021, 2399273121483, 150351458370, 0, 0, 0] := by
  rw [show A10K2.u6017 = KTree.node A10K2.u6013 (nat_lit 102127734) (nat_lit 8236973296) (nat_lit 0) A10K2.u6016 from rfl, totK_node, atot6013, atot6016]
  decide +kernel

theorem arows6024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6024 = true := by
  rw [show A10K2.u6024 = KTree.node A10K2.u6020 (nat_lit 102242541) (nat_lit 5878102410) (nat_lit 0) A10K2.u6023 from rfl, allE_node, arows6020, irow6024, arows6023]
  all_goals rfl

theorem atot6024 : totK PA10K2 A10K2.u6024 = [2176975535692, 9287691501530, 13061784511266, 7826837564208, 3988679867361, 1669732931365, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u6024 = KTree.node A10K2.u6020 (nat_lit 102242541) (nat_lit 5878102410) (nat_lit 0) A10K2.u6023 from rfl, totK_node, atot6020, atot6023]
  decide +kernel

theorem arows6032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6032 = true := by
  rw [show A10K2.u6032 = KTree.node A10K2.u6028 (nat_lit 102275105) (nat_lit 10069167935) (nat_lit 0) A10K2.u6031 from rfl, allE_node, arows6028, irow6032, arows6031]
  all_goals rfl

theorem atot6032 : totK PA10K2 A10K2.u6032 = [0, 3023373008149, 12396969288358, 15893914458835, 6640153287570, 902184975883, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u6032 = KTree.node A10K2.u6028 (nat_lit 102275105) (nat_lit 10069167935) (nat_lit 0) A10K2.u6031 from rfl, totK_node, atot6028, atot6031]
  decide +kernel

theorem arows6039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6039 = true := by
  rw [show A10K2.u6039 = KTree.node A10K2.u6035 (nat_lit 102329456) (nat_lit 14529291170) (nat_lit 0) A10K2.u6038 from rfl, allE_node, arows6035, irow6039, arows6038]
  all_goals rfl

theorem atot6039 : totK PA10K2 A10K2.u6039 = [1606735580082, 8289065632590, 15349514652489, 11795041542113, 3246501825317, 226700115334, 0, 0, 0, 0] := by
  rw [show A10K2.u6039 = KTree.node A10K2.u6035 (nat_lit 102329456) (nat_lit 14529291170) (nat_lit 0) A10K2.u6038 from rfl, totK_node, atot6035, atot6038]
  decide +kernel

theorem arows6048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6048 = true := by
  rw [show A10K2.u6048 = KTree.node A10K2.u6044 (nat_lit 102436509) (nat_lit 2892327891) (nat_lit 0) A10K2.u6047 from rfl, allE_node, arows6044, irow6048, arows6047]
  all_goals rfl

theorem atot6048 : totK PA10K2 A10K2.u6048 = [1572940895558, 7925531278751, 14411235976955, 11386644650670, 4015917126804, 622159644548, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6048 = KTree.node A10K2.u6044 (nat_lit 102436509) (nat_lit 2892327891) (nat_lit 0) A10K2.u6047 from rfl, totK_node, atot6044, atot6047]
  decide +kernel

theorem arows6055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6055 = true := by
  rw [show A10K2.u6055 = KTree.node A10K2.u6051 (nat_lit 102466481) (nat_lit 9107130710) (nat_lit 0) A10K2.u6054 from rfl, allE_node, arows6051, irow6055, arows6054]
  all_goals rfl

theorem atot6055 : totK PA10K2 A10K2.u6055 = [773825466003, 5314926161006, 13201057151095, 14070911369763, 5841073967862, 724606082095, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u6055 = KTree.node A10K2.u6051 (nat_lit 102466481) (nat_lit 9107130710) (nat_lit 0) A10K2.u6054 from rfl, totK_node, atot6051, atot6054]
  decide +kernel

theorem arows6063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6063 = true := by
  rw [show A10K2.u6063 = KTree.node A10K2.u6059 (nat_lit 102498628) (nat_lit 12811252744) (nat_lit 0) A10K2.u6062 from rfl, allE_node, arows6059, irow6063, arows6062]
  all_goals rfl

theorem atot6063 : totK PA10K2 A10K2.u6063 = [0, 2238196648567, 10269685984589, 15690409048814, 8997631037833, 1714725956231, 91890566284, 0, 0, 0] := by
  rw [show A10K2.u6063 = KTree.node A10K2.u6059 (nat_lit 102498628) (nat_lit 12811252744) (nat_lit 0) A10K2.u6062 from rfl, totK_node, atot6059, atot6062]
  decide +kernel

theorem arows6070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6070 = true := by
  rw [show A10K2.u6070 = KTree.node A10K2.u6066 (nat_lit 102531106) (nat_lit 5865201987) (nat_lit 0) A10K2.u6069 from rfl, allE_node, arows6066, irow6070, arows6069]
  all_goals rfl

theorem atot6070 : totK PA10K2 A10K2.u6070 = [0, 820549055654, 5917628051829, 14413946332779, 13333404360211, 4159094956998, 407892022564, 7007974415, 0, 0] := by
  rw [show A10K2.u6070 = KTree.node A10K2.u6066 (nat_lit 102531106) (nat_lit 5865201987) (nat_lit 0) A10K2.u6069 from rfl, totK_node, atot6066, atot6069]
  decide +kernel

theorem arows6080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6080 = true := by
  rw [show A10K2.u6080 = KTree.node A10K2.u6076 (nat_lit 102579611) (nat_lit 9617838488) (nat_lit 0) A10K2.u6079 from rfl, allE_node, arows6076, irow6080, arows6079]
  all_goals rfl

theorem atot6080 : totK PA10K2 A10K2.u6080 = [0, 1604737961340, 8402683334312, 15558468536019, 11798150467812, 3026499746903, 188516950054, 0, 0, 0] := by
  rw [show A10K2.u6080 = KTree.node A10K2.u6076 (nat_lit 102579611) (nat_lit 9617838488) (nat_lit 0) A10K2.u6079 from rfl, totK_node, atot6076, atot6079]
  decide +kernel

theorem arows6087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6087 = true := by
  rw [show A10K2.u6087 = KTree.node A10K2.u6083 (nat_lit 102695689) (nat_lit 9734790709) (nat_lit 0) A10K2.u6086 from rfl, allE_node, arows6083, irow6087, arows6086]
  all_goals rfl

theorem atot6087 : totK PA10K2 A10K2.u6087 = [0, 1463206879015, 7651485520431, 14610776700170, 12017920243234, 3871947106485, 390552732088, 7151180950, 0, 0] := by
  rw [show A10K2.u6087 = KTree.node A10K2.u6083 (nat_lit 102695689) (nat_lit 9734790709) (nat_lit 0) A10K2.u6086 from rfl, totK_node, atot6083, atot6086]
  decide +kernel

theorem arows6095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6095 = true := by
  rw [show A10K2.u6095 = KTree.node A10K2.u6091 (nat_lit 102727323) (nat_lit 8742797877) (nat_lit 0) A10K2.u6094 from rfl, allE_node, arows6091, irow6095, arows6094]
  all_goals rfl

theorem atot6095 : totK PA10K2 A10K2.u6095 = [0, 882069215384, 5979755832792, 14285130785187, 13875310513869, 4545051604335, 384689783727, 6318667960, 0, 0] := by
  rw [show A10K2.u6095 = KTree.node A10K2.u6091 (nat_lit 102727323) (nat_lit 8742797877) (nat_lit 0) A10K2.u6094 from rfl, totK_node, atot6091, atot6094]
  decide +kernel

theorem arows6102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6102 = true := by
  rw [show A10K2.u6102 = KTree.node A10K2.u6098 (nat_lit 102759879) (nat_lit 14488173040) (nat_lit 0) A10K2.u6101 from rfl, allE_node, arows6098, irow6102, arows6101]
  all_goals rfl

theorem atot6102 : totK PA10K2 A10K2.u6102 = [0, 1163774037120, 5811052479799, 11779041983336, 12424152654958, 6604833199750, 1278513906084, 67457817768, 0, 0] := by
  rw [show A10K2.u6102 = KTree.node A10K2.u6098 (nat_lit 102759879) (nat_lit 14488173040) (nat_lit 0) A10K2.u6101 from rfl, totK_node, atot6098, atot6101]
  decide +kernel

theorem arows6111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6111 = true := by
  rw [show A10K2.u6111 = KTree.node A10K2.u6107 (nat_lit 102789687) (nat_lit 14573984373) (nat_lit 0) A10K2.u6110 from rfl, allE_node, arows6107, irow6111, arows6110]
  all_goals rfl

theorem atot6111 : totK PA10K2 A10K2.u6111 = [0, 1175274676060, 6814040254351, 13901082705719, 11754594379144, 4072561612502, 602485400925, 30650496230, 0, 0] := by
  rw [show A10K2.u6111 = KTree.node A10K2.u6107 (nat_lit 102789687) (nat_lit 14573984373) (nat_lit 0) A10K2.u6110 from rfl, totK_node, atot6107, atot6110]
  decide +kernel

theorem arows6118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6118 = true := by
  rw [show A10K2.u6118 = KTree.node A10K2.u6114 (nat_lit 102821824) (nat_lit 14590704012) (nat_lit 0) A10K2.u6117 from rfl, allE_node, arows6114, irow6118, arows6117]
  all_goals rfl

theorem atot6118 : totK PA10K2 A10K2.u6118 = [0, 1088716171950, 6376404046450, 13820171039995, 12520844079314, 3954944922306, 361304525362, 5546304973, 0, 0] := by
  rw [show A10K2.u6118 = KTree.node A10K2.u6114 (nat_lit 102821824) (nat_lit 14590704012) (nat_lit 0) A10K2.u6117 from rfl, totK_node, atot6114, atot6117]
  decide +kernel

theorem arows6126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6126 = true := by
  rw [show A10K2.u6126 = KTree.node A10K2.u6122 (nat_lit 102927968) (nat_lit 13065288330) (nat_lit 0) A10K2.u6125 from rfl, allE_node, arows6122, irow6126, arows6125]
  all_goals rfl

theorem atot6126 : totK PA10K2 A10K2.u6126 = [0, 1318153661541, 7193230821147, 14202568956240, 11569131084153, 3210964075423, 275664555477, 5976421810, 0, 0] := by
  rw [show A10K2.u6126 = KTree.node A10K2.u6122 (nat_lit 102927968) (nat_lit 13065288330) (nat_lit 0) A10K2.u6125 from rfl, totK_node, atot6122, atot6125]
  decide +kernel

theorem arows6133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6133 = true := by
  rw [show A10K2.u6133 = KTree.node A10K2.u6129 (nat_lit 102982193) (nat_lit 9956268782) (nat_lit 0) A10K2.u6132 from rfl, allE_node, arows6129, irow6133, arows6132]
  all_goals rfl

theorem atot6133 : totK PA10K2 A10K2.u6133 = [0, 1551453506058, 8588727965711, 16101702408658, 11321530621783, 2487705237545, 126444518570, 0, 0, 0] := by
  rw [show A10K2.u6133 = KTree.node A10K2.u6129 (nat_lit 102982193) (nat_lit 9956268782) (nat_lit 0) A10K2.u6132 from rfl, totK_node, atot6129, atot6132]
  decide +kernel

theorem arows6148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6148 = true := by
  rw [show A10K2.u6148 = KTree.node A10K2.u6144 (nat_lit 103017869) (nat_lit 3588483070) (nat_lit 0) A10K2.u6147 from rfl, allE_node, arows6144, irow6148, arows6147]
  all_goals rfl

theorem atot6148 : totK PA10K2 A10K2.u6148 = [0, 0, 2520415982406, 11187151139311, 16245974373350, 8329787646744, 1339293674861, 61546239455, 0, 0] := by
  rw [show A10K2.u6148 = KTree.node A10K2.u6144 (nat_lit 103017869) (nat_lit 3588483070) (nat_lit 0) A10K2.u6147 from rfl, totK_node, atot6144, atot6147]
  decide +kernel

theorem arows6155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6155 = true := by
  rw [show A10K2.u6155 = KTree.node A10K2.u6151 (nat_lit 103048691) (nat_lit 4494081475) (nat_lit 0) A10K2.u6154 from rfl, allE_node, arows6151, irow6155, arows6154]
  all_goals rfl

theorem atot6155 : totK PA10K2 A10K2.u6155 = [0, 0, 1459439411711, 8060694979497, 15191359185483, 10628036717367, 2446450414135, 144190652462, 0, 0] := by
  rw [show A10K2.u6155 = KTree.node A10K2.u6151 (nat_lit 103048691) (nat_lit 4494081475) (nat_lit 0) A10K2.u6154 from rfl, totK_node, atot6151, atot6154]
  decide +kernel

theorem arows6163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6163 = true := by
  rw [show A10K2.u6163 = KTree.node A10K2.u6159 (nat_lit 103081458) (nat_lit 12855235688) (nat_lit 0) A10K2.u6162 from rfl, allE_node, arows6159, irow6163, arows6162]
  all_goals rfl

theorem atot6163 : totK PA10K2 A10K2.u6163 = [0, 0, 1041409727014, 6041136818639, 12736861325348, 11870136733714, 4808913218614, 777138984931, 36134558889, 0] := by
  rw [show A10K2.u6163 = KTree.node A10K2.u6159 (nat_lit 103081458) (nat_lit 12855235688) (nat_lit 0) A10K2.u6162 from rfl, totK_node, atot6159, atot6162]
  decide +kernel

theorem arows6170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6170 = true := by
  rw [show A10K2.u6170 = KTree.node A10K2.u6166 (nat_lit 103189267) (nat_lit 8567515457) (nat_lit 0) A10K2.u6169 from rfl, allE_node, arows6166, irow6170, arows6169]
  all_goals rfl

theorem atot6170 : totK PA10K2 A10K2.u6170 = [0, 0, 1155028352377, 6781199233144, 14303293443846, 11535241364692, 3016236240402, 278851241661, 5676195732, 0] := by
  rw [show A10K2.u6170 = KTree.node A10K2.u6166 (nat_lit 103189267) (nat_lit 8567515457) (nat_lit 0) A10K2.u6169 from rfl, totK_node, atot6166, atot6169]
  decide +kernel

theorem arows6179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6179 = true := by
  rw [show A10K2.u6179 = KTree.node A10K2.u6175 (nat_lit 103247067) (nat_lit 9161179912) (nat_lit 0) A10K2.u6178 from rfl, allE_node, arows6175, irow6179, arows6178]
  all_goals rfl

theorem atot6179 : totK PA10K2 A10K2.u6179 = [0, 838792425063, 5121152038900, 12247165614564, 13732584197087, 6646298843575, 1104069199301, 55561604187, 0, 0] := by
  rw [show A10K2.u6179 = KTree.node A10K2.u6175 (nat_lit 103247067) (nat_lit 9161179912) (nat_lit 0) A10K2.u6178 from rfl, totK_node, atot6175, atot6178]
  decide +kernel

theorem arows6186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6186 = true := by
  rw [show A10K2.u6186 = KTree.node A10K2.u6182 (nat_lit 103834508) (nat_lit 8305110947) (nat_lit 0) A10K2.u6185 from rfl, allE_node, arows6182, irow6186, arows6185]
  all_goals rfl

theorem atot6186 : totK PA10K2 A10K2.u6186 = [0, 1342466371279, 7590050010668, 14780587634230, 11328521094083, 3227898386438, 426812182850, 25239774317, 0, 0] := by
  rw [show A10K2.u6186 = KTree.node A10K2.u6182 (nat_lit 103834508) (nat_lit 8305110947) (nat_lit 0) A10K2.u6185 from rfl, totK_node, atot6182, atot6185]
  decide +kernel

theorem arows6194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6194 = true := by
  rw [show A10K2.u6194 = KTree.node A10K2.u6190 (nat_lit 103869888) (nat_lit 14874344913) (nat_lit 0) A10K2.u6193 from rfl, allE_node, arows6190, irow6194, arows6193]
  all_goals rfl

theorem atot6194 : totK PA10K2 A10K2.u6194 = [0, 1286023981050, 6462335436409, 13129522163434, 12423628537582, 4564395549345, 518242607565, 10957026886, 0, 0] := by
  rw [show A10K2.u6194 = KTree.node A10K2.u6190 (nat_lit 103869888) (nat_lit 14874344913) (nat_lit 0) A10K2.u6193 from rfl, totK_node, atot6190, atot6193]
  decide +kernel

theorem arows6201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6201 = true := by
  rw [show A10K2.u6201 = KTree.node A10K2.u6197 (nat_lit 103963294) (nat_lit 6146081271) (nat_lit 0) A10K2.u6200 from rfl, allE_node, arows6197, irow6201, arows6200]
  all_goals rfl

theorem atot6201 : totK PA10K2 A10K2.u6201 = [0, 859089464649, 6840233922345, 15374625907453, 11995603529862, 2704721961124, 158774606552, 0, 0, 0] := by
  rw [show A10K2.u6201 = KTree.node A10K2.u6197 (nat_lit 103963294) (nat_lit 6146081271) (nat_lit 0) A10K2.u6200 from rfl, totK_node, atot6197, atot6200]
  decide +kernel

theorem arows6211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6211 = true := by
  rw [show A10K2.u6211 = KTree.node A10K2.u6207 (nat_lit 104077655) (nat_lit 1174248817) (nat_lit 0) A10K2.u6210 from rfl, allE_node, arows6207, irow6211, arows6210]
  all_goals rfl

theorem atot6211 : totK PA10K2 A10K2.u6211 = [0, 0, 2293833116302, 10747120489282, 16040470679710, 7705986359534, 1150995669215, 43527332123, 0, 0] := by
  rw [show A10K2.u6211 = KTree.node A10K2.u6207 (nat_lit 104077655) (nat_lit 1174248817) (nat_lit 0) A10K2.u6210 from rfl, totK_node, atot6207, atot6210]
  decide +kernel

theorem arows6218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6218 = true := by
  rw [show A10K2.u6218 = KTree.node A10K2.u6214 (nat_lit 104211902) (nat_lit 15143782146) (nat_lit 0) A10K2.u6217 from rfl, allE_node, arows6214, irow6218, arows6217]
  all_goals rfl

theorem atot6218 : totK PA10K2 A10K2.u6218 = [0, 0, 2142506498390, 10569864334141, 16255068401554, 7871445643969, 1125943736677, 42962447115, 0, 0] := by
  rw [show A10K2.u6218 = KTree.node A10K2.u6214 (nat_lit 104211902) (nat_lit 15143782146) (nat_lit 0) A10K2.u6217 from rfl, totK_node, atot6214, atot6217]
  decide +kernel

theorem arows6226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6226 = true := by
  rw [show A10K2.u6226 = KTree.node A10K2.u6222 (nat_lit 104254316) (nat_lit 12608148872) (nat_lit 0) A10K2.u6225 from rfl, allE_node, arows6222, irow6226, arows6225]
  all_goals rfl

theorem atot6226 : totK PA10K2 A10K2.u6226 = [0, 835923233680, 3887850203196, 8225693597085, 11871551147707, 9457671302041, 2787448087681, 267717460541, 5976421810, 0] := by
  rw [show A10K2.u6226 = KTree.node A10K2.u6222 (nat_lit 104254316) (nat_lit 12608148872) (nat_lit 0) A10K2.u6225 from rfl, totK_node, atot6222, atot6225]
  decide +kernel

theorem arows6233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6233 = true := by
  rw [show A10K2.u6233 = KTree.node A10K2.u6229 (nat_lit 104362881) (nat_lit 10268712696) (nat_lit 0) A10K2.u6232 from rfl, allE_node, arows6229, irow6233, arows6232]
  all_goals rfl

theorem atot6233 : totK PA10K2 A10K2.u6233 = [0, 1341052302012, 7083099513444, 13853550675542, 11850412464522, 4209432969750, 619783658049, 30650496230, 0, 0] := by
  rw [show A10K2.u6233 = KTree.node A10K2.u6229 (nat_lit 104362881) (nat_lit 10268712696) (nat_lit 0) A10K2.u6232 from rfl, totK_node, atot6229, atot6232]
  decide +kernel

theorem arows6242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6242 = true := by
  rw [show A10K2.u6242 = KTree.node A10K2.u6238 (nat_lit 104410619) (nat_lit 6239094582) (nat_lit 0) A10K2.u6241 from rfl, allE_node, arows6238, irow6242, arows6241]
  all_goals rfl

theorem atot6242 : totK PA10K2 A10K2.u6242 = [0, 1606735580082, 8525897430154, 15769254850670, 11524911394231, 2724030379380, 170110738187, 0, 0, 0] := by
  rw [show A10K2.u6242 = KTree.node A10K2.u6238 (nat_lit 104410619) (nat_lit 6239094582) (nat_lit 0) A10K2.u6241 from rfl, totK_node, atot6238, atot6241]
  decide +kernel

theorem arows6249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6249 = true := by
  rw [show A10K2.u6249 = KTree.node A10K2.u6245 (nat_lit 104457721) (nat_lit 6023551604) (nat_lit 0) A10K2.u6248 from rfl, allE_node, arows6245, irow6249, arows6248]
  all_goals rfl

theorem atot6249 : totK PA10K2 A10K2.u6249 = [0, 1030662607010, 6124064393657, 13947260491295, 13538847574675, 4775420692271, 477924077159, 7380853412, 0, 0] := by
  rw [show A10K2.u6249 = KTree.node A10K2.u6245 (nat_lit 104457721) (nat_lit 6023551604) (nat_lit 0) A10K2.u6248 from rfl, totK_node, atot6245, atot6248]
  decide +kernel

theorem arows6257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6257 = true := by
  rw [show A10K2.u6257 = KTree.node A10K2.u6253 (nat_lit 104558592) (nat_lit 15703692072) (nat_lit 0) A10K2.u6256 from rfl, allE_node, arows6253, irow6257, arows6256]
  all_goals rfl

theorem atot6257 : totK PA10K2 A10K2.u6257 = [0, 1316103754551, 7529905192822, 14924343573483, 12123851238967, 3754705553271, 374869833595, 6904928264, 0, 0] := by
  rw [show A10K2.u6257 = KTree.node A10K2.u6253 (nat_lit 104558592) (nat_lit 15703692072) (nat_lit 0) A10K2.u6256 from rfl, totK_node, atot6253, atot6256]
  decide +kernel

theorem arows6264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6264 = true := by
  rw [show A10K2.u6264 = KTree.node A10K2.u6260 (nat_lit 104590847) (nat_lit 14004808951) (nat_lit 0) A10K2.u6263 from rfl, allE_node, arows6260, irow6264, arows6263]
  all_goals rfl

theorem atot6264 : totK PA10K2 A10K2.u6264 = [872244600920, 3408362204235, 5570025224386, 8972231327817, 12285906464072, 7306466844931, 1340822695065, 67876481508, 0, 0] := by
  rw [show A10K2.u6264 = KTree.node A10K2.u6260 (nat_lit 104590847) (nat_lit 14004808951) (nat_lit 0) A10K2.u6263 from rfl, totK_node, atot6260, atot6263]
  decide +kernel

theorem arows6275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6275 = true := by
  rw [show A10K2.u6275 = KTree.node A10K2.u6271 (nat_lit 105473175) (nat_lit 13759458355) (nat_lit 0) A10K2.u6274 from rfl, allE_node, arows6271, irow6275, arows6274]
  all_goals rfl

theorem atot6275 : totK PA10K2 A10K2.u6275 = [1471934576231, 8161573669283, 15468558919804, 11034811497213, 2458319583326, 133308759134, 0, 0, 0, 0] := by
  rw [show A10K2.u6275 = KTree.node A10K2.u6271 (nat_lit 105473175) (nat_lit 13759458355) (nat_lit 0) A10K2.u6274 from rfl, totK_node, atot6271, atot6274]
  decide +kernel

theorem arows6282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6282 = true := by
  rw [show A10K2.u6282 = KTree.node A10K2.u6278 (nat_lit 105502982) (nat_lit 5126204041) (nat_lit 0) A10K2.u6281 from rfl, allE_node, arows6278, irow6282, arows6281]
  all_goals rfl

theorem atot6282 : totK PA10K2 A10K2.u6282 = [830637671679, 4970955069360, 11815636198688, 13329213026028, 6180943865414, 911588008988, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6282 = KTree.node A10K2.u6278 (nat_lit 105502982) (nat_lit 5126204041) (nat_lit 0) A10K2.u6281 from rfl, totK_node, atot6278, atot6281]
  decide +kernel

theorem arows6290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6290 = true := by
  rw [show A10K2.u6290 = KTree.node A10K2.u6286 (nat_lit 105535656) (nat_lit 8804959660) (nat_lit 0) A10K2.u6289 from rfl, allE_node, arows6286, irow6290, arows6289]
  all_goals rfl

theorem atot6290 : totK PA10K2 A10K2.u6290 = [962840194868, 6827897380182, 15310255876258, 12309069267308, 2785100116241, 140445723896, 0, 0, 0, 0] := by
  rw [show A10K2.u6290 = KTree.node A10K2.u6286 (nat_lit 105535656) (nat_lit 8804959660) (nat_lit 0) A10K2.u6289 from rfl, totK_node, atot6286, atot6289]
  decide +kernel

theorem arows6297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6297 = true := by
  rw [show A10K2.u6297 = KTree.node A10K2.u6293 (nat_lit 105590231) (nat_lit 14388399796) (nat_lit 0) A10K2.u6296 from rfl, allE_node, arows6293, irow6297, arows6296]
  all_goals rfl

theorem atot6297 : totK PA10K2 A10K2.u6297 = [2170436959746, 9708874610623, 15133904916122, 9820386632091, 2715948740486, 317416528813, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6297 = KTree.node A10K2.u6293 (nat_lit 105590231) (nat_lit 14388399796) (nat_lit 0) A10K2.u6296 from rfl, totK_node, atot6293, atot6296]
  decide +kernel

theorem arows6306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6306 = true := by
  rw [show A10K2.u6306 = KTree.node A10K2.u6302 (nat_lit 105622925) (nat_lit 1383474258) (nat_lit 0) A10K2.u6305 from rfl, allE_node, arows6302, irow6306, arows6305]
  all_goals rfl

theorem atot6306 : totK PA10K2 A10K2.u6306 = [0, 2604592842249, 11610709447077, 16649270838991, 8282160829755, 1105965961675, 20018912194, 0, 0, 0] := by
  rw [show A10K2.u6306 = KTree.node A10K2.u6302 (nat_lit 105622925) (nat_lit 1383474258) (nat_lit 0) A10K2.u6305 from rfl, totK_node, atot6302, atot6305]
  decide +kernel

theorem arows6313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6313 = true := by
  rw [show A10K2.u6313 = KTree.node A10K2.u6309 (nat_lit 105725427) (nat_lit 8868770518) (nat_lit 0) A10K2.u6312 from rfl, allE_node, arows6309, irow6313, arows6312]
  all_goals rfl

theorem atot6313 : totK PA10K2 A10K2.u6313 = [0, 2340098393410, 10435597805715, 15556772328912, 8519855409652, 1589102759144, 93051590215, 0, 0, 0] := by
  rw [show A10K2.u6313 = KTree.node A10K2.u6309 (nat_lit 105725427) (nat_lit 8868770518) (nat_lit 0) A10K2.u6312 from rfl, totK_node, atot6309, atot6312]
  decide +kernel

theorem arows6321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6321 = true := by
  rw [show A10K2.u6321 = KTree.node A10K2.u6317 (nat_lit 105756963) (nat_lit 10160992118) (nat_lit 0) A10K2.u6320 from rfl, allE_node, arows6317, irow6321, arows6320]
  all_goals rfl

theorem atot6321 : totK PA10K2 A10K2.u6321 = [0, 0, 3103085296961, 12416857244589, 15462183951471, 6364140943647, 880810211675, 36704093874, 0, 0] := by
  rw [show A10K2.u6321 = KTree.node A10K2.u6317 (nat_lit 105756963) (nat_lit 10160992118) (nat_lit 0) A10K2.u6320 from rfl, totK_node, atot6317, atot6320]
  decide +kernel

theorem arows6328 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6328 = true := by
  rw [show A10K2.u6328 = KTree.node A10K2.u6324 (nat_lit 105790904) (nat_lit 12182704948) (nat_lit 0) A10K2.u6327 from rfl, allE_node, arows6324, irow6328, arows6327]
  all_goals rfl

theorem atot6328 : totK PA10K2 A10K2.u6328 = [0, 1793477866547, 9136393931776, 15418105691812, 9656324348977, 1935483592502, 107099009428, 0, 0, 0] := by
  rw [show A10K2.u6328 = KTree.node A10K2.u6324 (nat_lit 105790904) (nat_lit 12182704948) (nat_lit 0) A10K2.u6327 from rfl, totK_node, atot6324, atot6327]
  decide +kernel

theorem arows6338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6338 = true := by
  rw [show A10K2.u6338 = KTree.node A10K2.u6334 (nat_lit 105844620) (nat_lit 6124982003) (nat_lit 0) A10K2.u6337 from rfl, allE_node, arows6334, irow6338, arows6337]
  all_goals rfl

theorem atot6338 : totK PA10K2 A10K2.u6338 = [0, 1554005203789, 7681894468083, 14522735136139, 11765248378906, 3299993120946, 297009302455, 6239673734, 0, 0] := by
  rw [show A10K2.u6338 = KTree.node A10K2.u6334 (nat_lit 105844620) (nat_lit 6124982003) (nat_lit 0) A10K2.u6337 from rfl, totK_node, atot6334, atot6337]
  decide +kernel

theorem arows6345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6345 = true := by
  rw [show A10K2.u6345 = KTree.node A10K2.u6341 (nat_lit 105982216) (nat_lit 10581267868) (nat_lit 0) A10K2.u6344 from rfl, allE_node, arows6341, irow6345, arows6344]
  all_goals rfl

theorem atot6345 : totK PA10K2 A10K2.u6345 = [1592824415474, 7430778589642, 12853679516118, 10998660410444, 5192237041818, 1090806764068, 62382159641, 0, 0, 0] := by
  rw [show A10K2.u6345 = KTree.node A10K2.u6341 (nat_lit 105982216) (nat_lit 10581267868) (nat_lit 0) A10K2.u6344 from rfl, totK_node, atot6341, atot6344]
  decide +kernel

theorem arows6353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6353 = true := by
  rw [show A10K2.u6353 = KTree.node A10K2.u6349 (nat_lit 106014898) (nat_lit 15135211413) (nat_lit 0) A10K2.u6352 from rfl, allE_node, arows6349, irow6353, arows6352]
  all_goals rfl

theorem atot6353 : totK PA10K2 A10K2.u6353 = [595155796918, 4952662126513, 13322536612831, 13962585454561, 5369712872225, 716416185460, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u6353 = KTree.node A10K2.u6349 (nat_lit 106014898) (nat_lit 15135211413) (nat_lit 0) A10K2.u6352 from rfl, totK_node, atot6349, atot6352]
  decide +kernel

theorem arows6360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6360 = true := by
  rw [show A10K2.u6360 = KTree.node A10K2.u6356 (nat_lit 106043757) (nat_lit 6391208669) (nat_lit 0) A10K2.u6359 from rfl, allE_node, arows6356, irow6360, arows6359]
  all_goals rfl

theorem atot6360 : totK PA10K2 A10K2.u6360 = [1842378113796, 8461808775139, 14054575200117, 10538216802886, 3384139380875, 340478579593, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u6360 = KTree.node A10K2.u6356 (nat_lit 106043757) (nat_lit 6391208669) (nat_lit 0) A10K2.u6359 from rfl, totK_node, atot6356, atot6359]
  decide +kernel

theorem arows6369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6369 = true := by
  rw [show A10K2.u6369 = KTree.node A10K2.u6365 (nat_lit 106080951) (nat_lit 11063331853) (nat_lit 0) A10K2.u6368 from rfl, allE_node, arows6365, irow6369, arows6368]
  all_goals rfl

theorem atot6369 : totK PA10K2 A10K2.u6369 = [306750524226, 4715181339107, 14115266110476, 14078733782763, 4364241175083, 420218782709, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6369 = KTree.node A10K2.u6365 (nat_lit 106080951) (nat_lit 11063331853) (nat_lit 0) A10K2.u6368 from rfl, totK_node, atot6365, atot6368]
  decide +kernel

theorem arows6376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6376 = true := by
  rw [show A10K2.u6376 = KTree.node A10K2.u6372 (nat_lit 106254691) (nat_lit 8535951569) (nat_lit 0) A10K2.u6375 from rfl, allE_node, arows6372, irow6376, arows6375]
  all_goals rfl

theorem atot6376 : totK PA10K2 A10K2.u6376 = [0, 2269101028795, 10616587133306, 16154720694379, 8529501083027, 1299449988859, 44769798829, 0, 0, 0] := by
  rw [show A10K2.u6376 = KTree.node A10K2.u6372 (nat_lit 106254691) (nat_lit 8535951569) (nat_lit 0) A10K2.u6375 from rfl, totK_node, atot6372, atot6375]
  decide +kernel

theorem arows6384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6384 = true := by
  rw [show A10K2.u6384 = KTree.node A10K2.u6380 (nat_lit 106315891) (nat_lit 11933677) (nat_lit 0) A10K2.u6383 from rfl, allE_node, arows6380, irow6384, arows6383]
  all_goals rfl

theorem atot6384 : totK PA10K2 A10K2.u6384 = [0, 1585973059888, 8718096899201, 15700151742314, 9815719853866, 1819326093777, 98626162205, 0, 0, 0] := by
  rw [show A10K2.u6384 = KTree.node A10K2.u6380 (nat_lit 106315891) (nat_lit 11933677) (nat_lit 0) A10K2.u6383 from rfl, totK_node, atot6380, atot6383]
  decide +kernel

theorem arows6391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6391 = true := by
  rw [show A10K2.u6391 = KTree.node A10K2.u6387 (nat_lit 106430912) (nat_lit 15308065624) (nat_lit 0) A10K2.u6390 from rfl, allE_node, arows6387, irow6391, arows6390]
  all_goals rfl

theorem atot6391 : totK PA10K2 A10K2.u6391 = [1602700457968, 6502821453523, 9929588320941, 9757816283338, 7729231569413, 2743002321831, 347414729890, 6354482628, 0, 0] := by
  rw [show A10K2.u6391 = KTree.node A10K2.u6387 (nat_lit 106430912) (nat_lit 15308065624) (nat_lit 0) A10K2.u6390 from rfl, totK_node, atot6387, atot6390]
  decide +kernel

theorem arows6403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6403 = true := by
  rw [show A10K2.u6403 = KTree.node A10K2.u6399 (nat_lit 106469452) (nat_lit 10913712618) (nat_lit 0) A10K2.u6402 from rfl, allE_node, arows6399, irow6403, arows6402]
  all_goals rfl

theorem atot6403 : totK PA10K2 A10K2.u6403 = [838891203471, 5785697715279, 13818097853324, 13734676244494, 5125518609224, 695512819173, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u6403 = KTree.node A10K2.u6399 (nat_lit 106469452) (nat_lit 10913712618) (nat_lit 0) A10K2.u6402 from rfl, totK_node, atot6399, atot6402]
  decide +kernel

theorem arows6410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6410 = true := by
  rw [show A10K2.u6410 = KTree.node A10K2.u6406 (nat_lit 106522496) (nat_lit 12957959438) (nat_lit 0) A10K2.u6409 from rfl, allE_node, arows6406, irow6410, arows6409]
  all_goals rfl

theorem atot6410 : totK PA10K2 A10K2.u6410 = [1344116468241, 7815536018795, 15528012017523, 11746605153756, 2777430416546, 140498585709, 0, 0, 0, 0] := by
  rw [show A10K2.u6410 = KTree.node A10K2.u6406 (nat_lit 106522496) (nat_lit 12957959438) (nat_lit 0) A10K2.u6409 from rfl, totK_node, atot6406, atot6409]
  decide +kernel

theorem arows6418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6418 = true := by
  rw [show A10K2.u6418 = KTree.node A10K2.u6414 (nat_lit 106555106) (nat_lit 13708830069) (nat_lit 0) A10K2.u6417 from rfl, allE_node, arows6414, irow6418, arows6417]
  all_goals rfl

theorem atot6418 : totK PA10K2 A10K2.u6418 = [1087413459552, 5917541720839, 12623858544785, 12826856792592, 5752991329469, 901212629978, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6418 = KTree.node A10K2.u6414 (nat_lit 106555106) (nat_lit 13708830069) (nat_lit 0) A10K2.u6417 from rfl, totK_node, atot6414, atot6417]
  decide +kernel

theorem arows6425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6425 = true := by
  rw [show A10K2.u6425 = KTree.node A10K2.u6421 (nat_lit 106655789) (nat_lit 4098830132) (nat_lit 0) A10K2.u6424 from rfl, allE_node, arows6421, irow6425, arows6424]
  all_goals rfl

theorem atot6425 : totK PA10K2 A10K2.u6425 = [1259790066306, 7120688911744, 14470836679788, 12511689030846, 4211495741156, 446901583019, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6425 = KTree.node A10K2.u6421 (nat_lit 106655789) (nat_lit 4098830132) (nat_lit 0) A10K2.u6424 from rfl, totK_node, atot6421, atot6424]
  decide +kernel

theorem arows6434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6434 = true := by
  rw [show A10K2.u6434 = KTree.node A10K2.u6430 (nat_lit 106687956) (nat_lit 7196459548) (nat_lit 0) A10K2.u6433 from rfl, allE_node, arows6430, irow6434, arows6433]
  all_goals rfl

theorem atot6434 : totK PA10K2 A10K2.u6434 = [0, 2390908766324, 10811004476400, 16118208313317, 8824911375381, 1505318061349, 68157151558, 0, 0, 0] := by
  rw [show A10K2.u6434 = KTree.node A10K2.u6430 (nat_lit 106687956) (nat_lit 7196459548) (nat_lit 0) A10K2.u6433 from rfl, totK_node, atot6430, atot6433]
  decide +kernel

theorem arows6441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6441 = true := by
  rw [show A10K2.u6441 = KTree.node A10K2.u6437 (nat_lit 106725262) (nat_lit 15054305658) (nat_lit 0) A10K2.u6440 from rfl, allE_node, arows6437, irow6441, arows6440]
  all_goals rfl

theorem atot6441 : totK PA10K2 A10K2.u6441 = [0, 824587356464, 5925395700507, 14472900691762, 13990167046455, 4626326173437, 446504123935, 7007974415, 0, 0] := by
  rw [show A10K2.u6441 = KTree.node A10K2.u6437 (nat_lit 106725262) (nat_lit 15054305658) (nat_lit 0) A10K2.u6440 from rfl, totK_node, atot6437, atot6440]
  decide +kernel

theorem arows6449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6449 = true := by
  rw [show A10K2.u6449 = KTree.node A10K2.u6445 (nat_lit 106776677) (nat_lit 7148866666) (nat_lit 0) A10K2.u6448 from rfl, allE_node, arows6445, irow6449, arows6448]
  all_goals rfl

theorem atot6449 : totK PA10K2 A10K2.u6449 = [0, 2183007671712, 10133577089778, 15789011632869, 9269843162672, 1817638175028, 94510146812, 0, 0, 0] := by
  rw [show A10K2.u6449 = KTree.node A10K2.u6445 (nat_lit 106776677) (nat_lit 7148866666) (nat_lit 0) A10K2.u6448 from rfl, totK_node, atot6445, atot6448]
  decide +kernel

theorem arows6456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6456 = true := by
  rw [show A10K2.u6456 = KTree.node A10K2.u6452 (nat_lit 106815585) (nat_lit 7780843029) (nat_lit 0) A10K2.u6455 from rfl, allE_node, arows6452, irow6456, arows6455]
  all_goals rfl

theorem atot6456 : totK PA10K2 A10K2.u6456 = [0, 756035837065, 5529496830583, 13973690348424, 13991602504324, 4853052124027, 471972000527, 7151180950, 0, 0] := by
  rw [show A10K2.u6456 = KTree.node A10K2.u6452 (nat_lit 106815585) (nat_lit 7780843029) (nat_lit 0) A10K2.u6455 from rfl, totK_node, atot6452, atot6455]
  decide +kernel

theorem arows6466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6466 = true := by
  rw [show A10K2.u6466 = KTree.node A10K2.u6462 (nat_lit 106917048) (nat_lit 11718844091) (nat_lit 0) A10K2.u6465 from rfl, allE_node, arows6462, irow6466, arows6465]
  all_goals rfl

theorem atot6466 : totK PA10K2 A10K2.u6466 = [0, 1579996918481, 8322939141753, 15244455661206, 11470178440691, 3090753060919, 210819922373, 0, 0, 0] := by
  rw [show A10K2.u6466 = KTree.node A10K2.u6462 (nat_lit 106917048) (nat_lit 11718844091) (nat_lit 0) A10K2.u6465 from rfl, totK_node, atot6462, atot6465]
  decide +kernel

theorem arows6473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6473 = true := by
  rw [show A10K2.u6473 = KTree.node A10K2.u6469 (nat_lit 106948530) (nat_lit 14695277365) (nat_lit 0) A10K2.u6472 from rfl, allE_node, arows6469, irow6473, arows6472]
  all_goals rfl

theorem atot6473 : totK PA10K2 A10K2.u6473 = [0, 872244600920, 4736696449903, 11078193294534, 13637570582192, 7607123311748, 1418169373331, 73776485728, 0, 0] := by
  rw [show A10K2.u6473 = KTree.node A10K2.u6469 (nat_lit 106948530) (nat_lit 14695277365) (nat_lit 0) A10K2.u6472 from rfl, totK_node, atot6469, atot6472]
  decide +kernel

theorem arows6481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6481 = true := by
  rw [show A10K2.u6481 = KTree.node A10K2.u6477 (nat_lit 107567912) (nat_lit 11195828776) (nat_lit 0) A10K2.u6480 from rfl, allE_node, arows6477, irow6481, arows6480]
  all_goals rfl

theorem atot6481 : totK PA10K2 A10K2.u6481 = [0, 1471934576231, 8345053863886, 15698589066639, 10855423958919, 2299654182335, 112142339492, 0, 0, 0] := by
  rw [show A10K2.u6481 = KTree.node A10K2.u6477 (nat_lit 107567912) (nat_lit 11195828776) (nat_lit 0) A10K2.u6480 from rfl, totK_node, atot6477, atot6480]
  decide +kernel

theorem arows6488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6488 = true := by
  rw [show A10K2.u6488 = KTree.node A10K2.u6484 (nat_lit 107599132) (nat_lit 12116249641) (nat_lit 0) A10K2.u6487 from rfl, allE_node, arows6484, irow6488, arows6487]
  all_goals rfl

theorem atot6488 : totK PA10K2 A10K2.u6488 = [0, 724179001030, 4503604451882, 11724456426742, 13823158859219, 6198775369457, 902282014535, 37204059898, 0, 0] := by
  rw [show A10K2.u6488 = KTree.node A10K2.u6484 (nat_lit 107599132) (nat_lit 12116249641) (nat_lit 0) A10K2.u6487 from rfl, totK_node, atot6484, atot6487]
  decide +kernel

theorem arows6497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6497 = true := by
  rw [show A10K2.u6497 = KTree.node A10K2.u6493 (nat_lit 107631845) (nat_lit 7023573905) (nat_lit 0) A10K2.u6496 from rfl, allE_node, arows6493, irow6497, arows6496]
  all_goals rfl

theorem atot6497 : totK PA10K2 A10K2.u6497 = [0, 1069298865517, 7427089151596, 15664221561102, 11578352026054, 2442396110567, 114775681148, 0, 0, 0] := by
  rw [show A10K2.u6497 = KTree.node A10K2.u6493 (nat_lit 107631845) (nat_lit 7023573905) (nat_lit 0) A10K2.u6496 from rfl, totK_node, atot6493, atot6496]
  decide +kernel

theorem arows6504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6504 = true := by
  rw [show A10K2.u6504 = KTree.node A10K2.u6500 (nat_lit 107686989) (nat_lit 1215427645) (nat_lit 0) A10K2.u6503 from rfl, allE_node, arows6500, irow6504, arows6503]
  all_goals rfl

theorem atot6504 : totK PA10K2 A10K2.u6504 = [0, 2170436959746, 9528710959131, 14936550043727, 10033782271680, 2703184176272, 260169007647, 6354482628, 0, 0] := by
  rw [show A10K2.u6504 = KTree.node A10K2.u6500 (nat_lit 107686989) (nat_lit 1215427645) (nat_lit 0) A10K2.u6503 from rfl, totK_node, atot6500, atot6503]
  decide +kernel

theorem arows6512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6512 = true := by
  rw [show A10K2.u6512 = KTree.node A10K2.u6508 (nat_lit 107720087) (nat_lit 14535722111) (nat_lit 0) A10K2.u6511 from rfl, allE_node, arows6508, irow6512, arows6511]
  all_goals rfl

theorem atot6512 : totK PA10K2 A10K2.u6512 = [0, 0, 2780006420063, 12169547549535, 16698411841944, 7664691805710, 878469368544, 13204174009, 0, 0] := by
  rw [show A10K2.u6512 = KTree.node A10K2.u6508 (nat_lit 107720087) (nat_lit 14535722111) (nat_lit 0) A10K2.u6511 from rfl, totK_node, atot6508, atot6511]
  decide +kernel

theorem arows6519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6519 = true := by
  rw [show A10K2.u6519 = KTree.node A10K2.u6515 (nat_lit 107823656) (nat_lit 9109752117) (nat_lit 0) A10K2.u6518 from rfl, allE_node, arows6515, irow6519, arows6518]
  all_goals rfl

theorem atot6519 : totK PA10K2 A10K2.u6519 = [0, 0, 2327608893552, 10517011849933, 15590887032642, 8320908441607, 1470575601869, 72981569056, 0, 0] := by
  rw [show A10K2.u6519 = KTree.node A10K2.u6515 (nat_lit 107823656) (nat_lit 9109752117) (nat_lit 0) A10K2.u6518 from rfl, totK_node, atot6515, atot6518]
  decide +kernel

theorem arows6530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6530 = true := by
  rw [show A10K2.u6530 = KTree.node A10K2.u6526 (nat_lit 107855359) (nat_lit 10192301131) (nat_lit 0) A10K2.u6529 from rfl, allE_node, arows6526, irow6530, arows6529]
  all_goals rfl

theorem atot6530 : totK PA10K2 A10K2.u6530 = [0, 0, 251986720587, 3672807119668, 12136798403998, 14604454431668, 6148901620058, 895537805769, 36704093874, 0] := by
  rw [show A10K2.u6530 = KTree.node A10K2.u6526 (nat_lit 107855359) (nat_lit 10192301131) (nat_lit 0) A10K2.u6529 from rfl, totK_node, atot6526, atot6529]
  decide +kernel

theorem arows6537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6537 = true := by
  rw [show A10K2.u6537 = KTree.node A10K2.u6533 (nat_lit 107890007) (nat_lit 5787873980) (nat_lit 0) A10K2.u6536 from rfl, allE_node, arows6533, irow6537, arows6536]
  all_goals rfl

theorem atot6537 : totK PA10K2 A10K2.u6537 = [0, 0, 1535201939645, 8483370230473, 15677778882614, 10230552207190, 1910480863019, 88935986884, 0, 0] := by
  rw [show A10K2.u6537 = KTree.node A10K2.u6533 (nat_lit 107890007) (nat_lit 5787873980) (nat_lit 0) A10K2.u6536 from rfl, totK_node, atot6533, atot6536]
  decide +kernel

theorem arows6545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6545 = true := by
  rw [show A10K2.u6545 = KTree.node A10K2.u6541 (nat_lit 107948397) (nat_lit 6163917128) (nat_lit 0) A10K2.u6544 from rfl, allE_node, arows6541, irow6545, arows6544]
  all_goals rfl

theorem atot6545 : totK PA10K2 A10K2.u6545 = [0, 0, 2162382547954, 9593104209239, 14830654557835, 9734070672677, 2493807484533, 250889899636, 5982052406, 0] := by
  rw [show A10K2.u6545 = KTree.node A10K2.u6541 (nat_lit 107948397) (nat_lit 6163917128) (nat_lit 0) A10K2.u6544 from rfl, totK_node, atot6541, atot6544]
  decide +kernel

theorem arows6552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6552 = true := by
  rw [show A10K2.u6552 = KTree.node A10K2.u6548 (nat_lit 108084678) (nat_lit 15249006711) (nat_lit 0) A10K2.u6551 from rfl, allE_node, arows6548, irow6552, arows6551]
  all_goals rfl

theorem atot6552 : totK PA10K2 A10K2.u6552 = [0, 2187980212392, 9747448812492, 14538308084902, 8836649753833, 3005089007604, 632684573945, 41590655314, 0, 0] := by
  rw [show A10K2.u6552 = KTree.node A10K2.u6548 (nat_lit 108084678) (nat_lit 15249006711) (nat_lit 0) A10K2.u6551 from rfl, totK_node, atot6548, atot6551]
  decide +kernel

theorem arows6561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6561 = true := by
  rw [show A10K2.u6561 = KTree.node A10K2.u6557 (nat_lit 108117460) (nat_lit 8038786286) (nat_lit 0) A10K2.u6560 from rfl, allE_node, arows6557, irow6561, arows6560]
  all_goals rfl

theorem atot6561 : totK PA10K2 A10K2.u6561 = [0, 247698060303, 3217630008463, 11653892532475, 15577433121462, 6976061265469, 953655634800, 37204059898, 0, 0] := by
  rw [show A10K2.u6561 = KTree.node A10K2.u6557 (nat_lit 108117460) (nat_lit 8038786286) (nat_lit 0) A10K2.u6560 from rfl, totK_node, atot6557, atot6560]
  decide +kernel

theorem arows6568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6568 = true := by
  rw [show A10K2.u6568 = KTree.node A10K2.u6564 (nat_lit 108148586) (nat_lit 9713072085) (nat_lit 0) A10K2.u6567 from rfl, allE_node, arows6564, irow6568, arows6567]
  all_goals rfl

theorem atot6568 : totK PA10K2 A10K2.u6568 = [0, 1901430577719, 9621761217113, 15840851882280, 9112532588299, 1617181766530, 88342950191, 0, 0, 0] := by
  rw [show A10K2.u6568 = KTree.node A10K2.u6564 (nat_lit 108148586) (nat_lit 9713072085) (nat_lit 0) A10K2.u6567 from rfl, totK_node, atot6564, atot6567]
  decide +kernel

theorem arows6576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6576 = true := by
  rw [show A10K2.u6576 = KTree.node A10K2.u6572 (nat_lit 108187987) (nat_lit 8846375758) (nat_lit 0) A10K2.u6575 from rfl, allE_node, arows6572, irow6576, arows6575]
  all_goals rfl

theorem atot6576 : totK PA10K2 A10K2.u6576 = [0, 0, 2779580068880, 11726434827017, 15672084951884, 6822731608163, 980950180410, 37807056478, 0, 0] := by
  rw [show A10K2.u6576 = KTree.node A10K2.u6572 (nat_lit 108187987) (nat_lit 8846375758) (nat_lit 0) A10K2.u6575 from rfl, totK_node, atot6572, atot6575]
  decide +kernel

theorem arows6583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6583 = true := by
  rw [show A10K2.u6583 = KTree.node A10K2.u6579 (nat_lit 108361182) (nat_lit 14503553104) (nat_lit 0) A10K2.u6582 from rfl, allE_node, arows6579, irow6583, arows6582]
  all_goals rfl

theorem atot6583 : totK PA10K2 A10K2.u6583 = [0, 0, 2599580491415, 11619275529241, 16286043964114, 7205451461965, 858292331724, 18777717872, 0, 0] := by
  rw [show A10K2.u6583 = KTree.node A10K2.u6579 (nat_lit 108361182) (nat_lit 14503553104) (nat_lit 0) A10K2.u6582 from rfl, totK_node, atot6579, atot6582]
  decide +kernel

theorem arows6593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6593 = true := by
  rw [show A10K2.u6593 = KTree.node A10K2.u6589 (nat_lit 108429369) (nat_lit 7339380254) (nat_lit 0) A10K2.u6592 from rfl, allE_node, arows6589, irow6593, arows6592]
  all_goals rfl

theorem atot6593 : totK PA10K2 A10K2.u6593 = [0, 0, 819213633141, 6557679564345, 15449369212369, 11713700169411, 2485758597878, 129831166052, 0, 0] := by
  rw [show A10K2.u6593 = KTree.node A10K2.u6589 (nat_lit 108429369) (nat_lit 7339380254) (nat_lit 0) A10K2.u6592 from rfl, totK_node, atot6589, atot6592]
  decide +kernel

theorem arows6600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6600 = true := by
  rw [show A10K2.u6600 = KTree.node A10K2.u6596 (nat_lit 108553118) (nat_lit 15030548709) (nat_lit 0) A10K2.u6599 from rfl, allE_node, arows6596, irow6600, arows6599]
  all_goals rfl

theorem atot6600 : totK PA10K2 A10K2.u6600 = [0, 1602700457968, 8252529046720, 14525299603579, 10313591291358, 3747357384465, 1217393544761, 203361510298, 6354482628, 0] := by
  rw [show A10K2.u6600 = KTree.node A10K2.u6596 (nat_lit 108553118) (nat_lit 15030548709) (nat_lit 0) A10K2.u6599 from rfl, totK_node, atot6596, atot6599]
  decide +kernel

theorem arows6608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6608 = true := by
  rw [show A10K2.u6608 = KTree.node A10K2.u6604 (nat_lit 108604563) (nat_lit 10901359787) (nat_lit 0) A10K2.u6607 from rfl, allE_node, arows6604, irow6608, arows6607]
  all_goals rfl

theorem atot6608 : totK PA10K2 A10K2.u6608 = [0, 1568181643020, 7720589809770, 14122224969635, 11513750228899, 3775703643065, 399248748928, 7237400819, 0, 0] := by
  rw [show A10K2.u6608 = KTree.node A10K2.u6604 (nat_lit 108604563) (nat_lit 10901359787) (nat_lit 0) A10K2.u6607 from rfl, totK_node, atot6604, atot6607]
  decide +kernel

theorem arows6615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6615 = true := by
  rw [show A10K2.u6615 = KTree.node A10K2.u6611 (nat_lit 108636854) (nat_lit 15076288878) (nat_lit 0) A10K2.u6614 from rfl, allE_node, arows6611, irow6615, arows6614]
  all_goals rfl

theorem atot6615 : totK PA10K2 A10K2.u6615 = [0, 614826028692, 4776595651823, 12665159458690, 13973538099225, 6027861051870, 885845307376, 36968589557, 0, 0] := by
  rw [show A10K2.u6615 = KTree.node A10K2.u6611 (nat_lit 108636854) (nat_lit 15076288878) (nat_lit 0) A10K2.u6614 from rfl, totK_node, atot6611, atot6614]
  decide +kernel

theorem arows6624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6624 = true := by
  rw [show A10K2.u6624 = KTree.node A10K2.u6620 (nat_lit 108733664) (nat_lit 4268463531) (nat_lit 0) A10K2.u6623 from rfl, allE_node, arows6620, irow6624, arows6623]
  all_goals rfl

theorem atot6624 : totK PA10K2 A10K2.u6624 = [0, 2134774689524, 9811737563837, 15732631571208, 9987712668003, 2234043592550, 126899255655, 0, 0, 0] := by
  rw [show A10K2.u6624 = KTree.node A10K2.u6620 (nat_lit 108733664) (nat_lit 4268463531) (nat_lit 0) A10K2.u6623 from rfl, totK_node, atot6620, atot6623]
  decide +kernel

theorem arows6631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6631 = true := by
  rw [show A10K2.u6631 = KTree.node A10K2.u6627 (nat_lit 108761637) (nat_lit 6154421336) (nat_lit 0) A10K2.u6630 from rfl, allE_node, arows6627, irow6631, arows6630]
  all_goals rfl

theorem atot6631 : totK PA10K2 A10K2.u6631 = [0, 203085421841, 3824952681296, 13058486976639, 15624786696173, 6494203274047, 728538450238, 13679205470, 0, 0] := by
  rw [show A10K2.u6631 = KTree.node A10K2.u6627 (nat_lit 108761637) (nat_lit 6154421336) (nat_lit 0) A10K2.u6630 from rfl, totK_node, atot6627, atot6630]
  decide +kernel

theorem arows6639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6639 = true := by
  rw [show A10K2.u6639 = KTree.node A10K2.u6635 (nat_lit 113249715) (nat_lit 8272353185) (nat_lit 0) A10K2.u6638 from rfl, allE_node, arows6635, irow6639, arows6638]
  all_goals rfl

theorem atot6639 : totK PA10K2 A10K2.u6639 = [1615265915188, 7080184287160, 10668025308245, 7811382974089, 6137478354818, 4130009333814, 979638778335, 61110126106, 0, 0] := by
  rw [show A10K2.u6639 = KTree.node A10K2.u6635 (nat_lit 113249715) (nat_lit 8272353185) (nat_lit 0) A10K2.u6638 from rfl, totK_node, atot6635, atot6638]
  decide +kernel

theorem arows6646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6646 = true := by
  rw [show A10K2.u6646 = KTree.node A10K2.u6642 (nat_lit 113281685) (nat_lit 4645656547) (nat_lit 0) A10K2.u6645 from rfl, allE_node, arows6642, irow6646, arows6645]
  all_goals rfl

theorem atot6646 : totK PA10K2 A10K2.u6646 = [616560319149, 4717107789939, 12621763996327, 14060184646181, 5874407984470, 794002988043, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u6646 = KTree.node A10K2.u6642 (nat_lit 113281685) (nat_lit 4645656547) (nat_lit 0) A10K2.u6645 from rfl, totK_node, atot6642, atot6645]
  decide +kernel

theorem arows6659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6659 = true := by
  rw [show A10K2.u6659 = KTree.node A10K2.u6655 (nat_lit 113383709) (nat_lit 6358536594) (nat_lit 0) A10K2.u6658 from rfl, allE_node, arows6655, irow6659, arows6658]
  all_goals rfl

theorem atot6659 : totK PA10K2 A10K2.u6659 = [1318949507170, 7786698524743, 15379196052264, 11528394992738, 2895350009256, 234177454239, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u6659 = KTree.node A10K2.u6655 (nat_lit 113383709) (nat_lit 6358536594) (nat_lit 0) A10K2.u6658 from rfl, totK_node, atot6655, atot6658]
  decide +kernel

theorem arows6666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6666 = true := by
  rw [show A10K2.u6666 = KTree.node A10K2.u6662 (nat_lit 113448993) (nat_lit 10069167935) (nat_lit 0) A10K2.u6665 from rfl, allE_node, arows6662, irow6666, arows6665]
  all_goals rfl

theorem atot6666 : totK PA10K2 A10K2.u6666 = [2086733268503, 9269099980802, 14748672010913, 10019051286147, 2768725294604, 319911379868, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6666 = KTree.node A10K2.u6662 (nat_lit 113448993) (nat_lit 10069167935) (nat_lit 0) A10K2.u6665 from rfl, totK_node, atot6662, atot6665]
  decide +kernel

theorem arows6674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6674 = true := by
  rw [show A10K2.u6674 = KTree.node A10K2.u6670 (nat_lit 113479789) (nat_lit 5243544936) (nat_lit 0) A10K2.u6673 from rfl, allE_node, arows6670, irow6674, arows6673]
  all_goals rfl

theorem atot6674 : totK PA10K2 A10K2.u6674 = [165731654200, 3618626867998, 12746681589310, 15697995351428, 6809569655444, 804896368230, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u6674 = KTree.node A10K2.u6670 (nat_lit 113479789) (nat_lit 5243544936) (nat_lit 0) A10K2.u6673 from rfl, totK_node, atot6670, atot6673]
  decide +kernel

theorem arows6681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6681 = true := by
  rw [show A10K2.u6681 = KTree.node A10K2.u6677 (nat_lit 113512054) (nat_lit 16090012373) (nat_lit 0) A10K2.u6680 from rfl, allE_node, arows6677, irow6681, arows6680]
  all_goals rfl

theorem atot6681 : totK PA10K2 A10K2.u6681 = [0, 2054209885945, 9692370565020, 15508488821319, 9330638981491, 1818005781234, 97646819907, 0, 0, 0] := by
  rw [show A10K2.u6681 = KTree.node A10K2.u6677 (nat_lit 113512054) (nat_lit 16090012373) (nat_lit 0) A10K2.u6680 from rfl, totK_node, atot6677, atot6680]
  decide +kernel

theorem arows6690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6690 = true := by
  rw [show A10K2.u6690 = KTree.node A10K2.u6686 (nat_lit 113544698) (nat_lit 11837886838) (nat_lit 0) A10K2.u6689 from rfl, allE_node, arows6686, irow6690, arows6689]
  all_goals rfl

theorem atot6690 : totK PA10K2 A10K2.u6690 = [0, 504850548399, 4563179497392, 12753145008417, 13861624820757, 5651879291970, 838421781333, 36134558889, 0, 0] := by
  rw [show A10K2.u6690 = KTree.node A10K2.u6686 (nat_lit 113544698) (nat_lit 11837886838) (nat_lit 0) A10K2.u6689 from rfl, totK_node, atot6686, atot6689]
  decide +kernel

theorem arows6697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6697 = true := by
  rw [show A10K2.u6697 = KTree.node A10K2.u6693 (nat_lit 113656311) (nat_lit 11483131506) (nat_lit 0) A10K2.u6696 from rfl, allE_node, arows6693, irow6697, arows6696]
  all_goals rfl

theorem atot6697 : totK PA10K2 A10K2.u6697 = [0, 1318074694865, 7922710198417, 15633455567960, 11268494082755, 2476632421551, 144382811204, 0, 0, 0] := by
  rw [show A10K2.u6697 = KTree.node A10K2.u6693 (nat_lit 113656311) (nat_lit 11483131506) (nat_lit 0) A10K2.u6696 from rfl, totK_node, atot6693, atot6696]
  decide +kernel

theorem arows6705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6705 = true := by
  rw [show A10K2.u6705 = KTree.node A10K2.u6701 (nat_lit 113714844) (nat_lit 11040144392) (nat_lit 0) A10K2.u6704 from rfl, allE_node, arows6701, irow6705, arows6704]
  all_goals rfl

theorem atot6705 : totK PA10K2 A10K2.u6705 = [0, 2252187420121, 9930629813618, 15242708985856, 9471408908707, 2339311437561, 225349401419, 5676195732, 0, 0] := by
  rw [show A10K2.u6705 = KTree.node A10K2.u6701 (nat_lit 113714844) (nat_lit 11040144392) (nat_lit 0) A10K2.u6704 from rfl, totK_node, atot6701, atot6704]
  decide +kernel

theorem arows6712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6712 = true := by
  rw [show A10K2.u6712 = KTree.node A10K2.u6708 (nat_lit 113851201) (nat_lit 3276928428) (nat_lit 0) A10K2.u6711 from rfl, allE_node, arows6708, irow6712, arows6711]
  all_goals rfl

theorem atot6712 : totK PA10K2 A10K2.u6712 = [2238164317933, 9633790388998, 14131210528244, 8804596092436, 3358964932009, 799020976842, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u6712 = KTree.node A10K2.u6708 (nat_lit 113851201) (nat_lit 3276928428) (nat_lit 0) A10K2.u6711 from rfl, totK_node, atot6708, atot6711]
  decide +kernel

theorem arows6722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6722 = true := by
  rw [show A10K2.u6722 = KTree.node A10K2.u6718 (nat_lit 113883293) (nat_lit 6237309011) (nat_lit 0) A10K2.u6721 from rfl, allE_node, arows6718, irow6722, arows6721]
  all_goals rfl

theorem atot6722 : totK PA10K2 A10K2.u6722 = [0, 3035563920692, 12251674270652, 15727752371608, 6825471716777, 940356164833, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6722 = KTree.node A10K2.u6718 (nat_lit 113883293) (nat_lit 6237309011) (nat_lit 0) A10K2.u6721 from rfl, totK_node, atot6718, atot6721]
  decide +kernel

theorem arows6729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6729 = true := by
  rw [show A10K2.u6729 = KTree.node A10K2.u6725 (nat_lit 113920301) (nat_lit 6651382109) (nat_lit 0) A10K2.u6728 from rfl, allE_node, arows6725, irow6729, arows6728]
  all_goals rfl

theorem atot6729 : totK PA10K2 A10K2.u6729 = [1323934157412, 7479024855045, 14927764741530, 11958431169093, 3123410753399, 199929857190, 0, 0, 0, 0] := by
  rw [show A10K2.u6729 = KTree.node A10K2.u6725 (nat_lit 113920301) (nat_lit 6651382109) (nat_lit 0) A10K2.u6728 from rfl, totK_node, atot6725, atot6728]
  decide +kernel

theorem arows6737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6737 = true := by
  rw [show A10K2.u6737 = KTree.node A10K2.u6733 (nat_lit 113979094) (nat_lit 15136587392) (nat_lit 0) A10K2.u6736 from rfl, allE_node, arows6733, irow6737, arows6736]
  all_goals rfl

theorem atot6737 : totK PA10K2 A10K2.u6737 = [2253625996168, 10200582871723, 15567323083216, 9209180856305, 2182668784648, 256570509282, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6737 = KTree.node A10K2.u6733 (nat_lit 113979094) (nat_lit 15136587392) (nat_lit 0) A10K2.u6736 from rfl, totK_node, atot6733, atot6736]
  decide +kernel

theorem arows6744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6744 = true := by
  rw [show A10K2.u6744 = KTree.node A10K2.u6740 (nat_lit 114011150) (nat_lit 14654016581) (nat_lit 0) A10K2.u6743 from rfl, allE_node, arows6740, irow6744, arows6743]
  all_goals rfl

theorem atot6744 : totK PA10K2 A10K2.u6744 = [0, 2578251789127, 11540842310329, 16547282320301, 8108257957538, 1049725671782, 20018912194, 0, 0, 0] := by
  rw [show A10K2.u6744 = KTree.node A10K2.u6740 (nat_lit 114011150) (nat_lit 14654016581) (nat_lit 0) A10K2.u6743 from rfl, totK_node, atot6740, atot6743]
  decide +kernel

theorem arows6753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6753 = true := by
  rw [show A10K2.u6753 = KTree.node A10K2.u6749 (nat_lit 114113648) (nat_lit 12030131756) (nat_lit 0) A10K2.u6752 from rfl, allE_node, arows6749, irow6753, arows6752]
  all_goals rfl

theorem atot6753 : totK PA10K2 A10K2.u6753 = [0, 2236209084854, 10231909791810, 15697877353960, 8952012727358, 1695443197739, 93051590215, 0, 0, 0] := by
  rw [show A10K2.u6753 = KTree.node A10K2.u6749 (nat_lit 114113648) (nat_lit 12030131756) (nat_lit 0) A10K2.u6752 from rfl, totK_node, atot6749, atot6752]
  decide +kernel

theorem arows6760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6760 = true := by
  rw [show A10K2.u6760 = KTree.node A10K2.u6756 (nat_lit 114145949) (nat_lit 5830957283) (nat_lit 0) A10K2.u6759 from rfl, allE_node, arows6756, irow6760, arows6759]
  all_goals rfl

theorem atot6760 : totK PA10K2 A10K2.u6760 = [0, 304922396905, 3563412271320, 12147654765313, 15078140035727, 6454634014711, 912086367573, 36704093874, 0, 0] := by
  rw [show A10K2.u6760 = KTree.node A10K2.u6756 (nat_lit 114145949) (nat_lit 5830957283) (nat_lit 0) A10K2.u6759 from rfl, totK_node, atot6756, atot6759]
  decide +kernel

theorem arows6768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6768 = true := by
  rw [show A10K2.u6768 = KTree.node A10K2.u6764 (nat_lit 114186275) (nat_lit 8490105759) (nat_lit 0) A10K2.u6767 from rfl, allE_node, arows6764, irow6768, arows6767]
  all_goals rfl

theorem atot6768 : totK PA10K2 A10K2.u6768 = [0, 1205744620323, 7245495482882, 14735388305040, 11792331004943, 3264275767440, 305877516256, 6239673734, 0, 0] := by
  rw [show A10K2.u6768 = KTree.node A10K2.u6764 (nat_lit 114186275) (nat_lit 8490105759) (nat_lit 0) A10K2.u6767 from rfl, totK_node, atot6764, atot6767]
  decide +kernel

theorem arows6775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6775 = true := by
  rw [show A10K2.u6775 = KTree.node A10K2.u6771 (nat_lit 114243424) (nat_lit 5586307556) (nat_lit 0) A10K2.u6774 from rfl, allE_node, arows6771, irow6775, arows6774]
  all_goals rfl

theorem atot6775 : totK PA10K2 A10K2.u6775 = [0, 2065444566941, 10049739151899, 16369110136077, 9731594934217, 1699721873542, 57387911025, 0, 0, 0] := by
  rw [show A10K2.u6775 = KTree.node A10K2.u6771 (nat_lit 114243424) (nat_lit 5586307556) (nat_lit 0) A10K2.u6774 from rfl, totK_node, atot6771, atot6774]
  decide +kernel

theorem arows6786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6786 = true := by
  rw [show A10K2.u6786 = KTree.node A10K2.u6782 (nat_lit 114837864) (nat_lit 9742723058) (nat_lit 0) A10K2.u6785 from rfl, allE_node, arows6782, irow6786, arows6785]
  all_goals rfl

theorem atot6786 : totK PA10K2 A10K2.u6786 = [2080970604401, 9689761613448, 15382467187402, 9400442086698, 2239659276256, 399955553445, 43287591117, 0, 0, 0] := by
  rw [show A10K2.u6786 = KTree.node A10K2.u6782 (nat_lit 114837864) (nat_lit 9742723058) (nat_lit 0) A10K2.u6785 from rfl, totK_node, atot6782, atot6785]
  decide +kernel

theorem arows6793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6793 = true := by
  rw [show A10K2.u6793 = KTree.node A10K2.u6789 (nat_lit 114872420) (nat_lit 12963945183) (nat_lit 0) A10K2.u6792 from rfl, allE_node, arows6789, irow6793, arows6792]
  all_goals rfl

theorem atot6793 : totK PA10K2 A10K2.u6793 = [811040046021, 5221627628524, 12471939165258, 13372501758967, 5792048150188, 881333725972, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u6793 = KTree.node A10K2.u6789 (nat_lit 114872420) (nat_lit 12963945183) (nat_lit 0) A10K2.u6792 from rfl, totK_node, atot6789, atot6792]
  decide +kernel

theorem arows6801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6801 = true := by
  rw [show A10K2.u6801 = KTree.node A10K2.u6797 (nat_lit 114912696) (nat_lit 13966343215) (nat_lit 0) A10K2.u6800 from rfl, allE_node, arows6797, irow6801, arows6800]
  all_goals rfl

theorem atot6801 : totK PA10K2 A10K2.u6801 = [1277311426415, 7411789816138, 15127389156404, 12134565717681, 3217198421948, 195379683689, 0, 0, 0, 0] := by
  rw [show A10K2.u6801 = KTree.node A10K2.u6797 (nat_lit 114912696) (nat_lit 13966343215) (nat_lit 0) A10K2.u6800 from rfl, totK_node, atot6797, atot6800]
  decide +kernel

theorem arows6808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6808 = true := by
  rw [show A10K2.u6808 = KTree.node A10K2.u6804 (nat_lit 114945719) (nat_lit 14878049232) (nat_lit 0) A10K2.u6807 from rfl, allE_node, arows6804, irow6808, arows6807]
  all_goals rfl

theorem atot6808 : totK PA10K2 A10K2.u6808 = [1300028584640, 6695667206581, 13029088528323, 11903463305437, 5013416491637, 813586519387, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6808 = KTree.node A10K2.u6804 (nat_lit 114945719) (nat_lit 14878049232) (nat_lit 0) A10K2.u6807 from rfl, totK_node, atot6804, atot6807]
  decide +kernel

theorem arows6817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6817 = true := by
  rw [show A10K2.u6817 = KTree.node A10K2.u6813 (nat_lit 115044869) (nat_lit 5787146262) (nat_lit 0) A10K2.u6816 from rfl, allE_node, arows6813, irow6817, arows6816]
  all_goals rfl

theorem atot6817 : totK PA10K2 A10K2.u6817 = [1124207821172, 6661709041452, 14277371536202, 12851299900027, 4313635534024, 425717466389, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u6817 = KTree.node A10K2.u6813 (nat_lit 115044869) (nat_lit 5787146262) (nat_lit 0) A10K2.u6816 from rfl, totK_node, atot6813, atot6816]
  decide +kernel

theorem arows6824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6824 = true := by
  rw [show A10K2.u6824 = KTree.node A10K2.u6820 (nat_lit 115076531) (nat_lit 9562641334) (nat_lit 0) A10K2.u6823 from rfl, allE_node, arows6820, irow6824, arows6823]
  all_goals rfl

theorem atot6824 : totK PA10K2 A10K2.u6824 = [0, 2466819647160, 10886364436539, 15875834499174, 8595826542381, 1484675455210, 68157151558, 0, 0, 0] := by
  rw [show A10K2.u6824 = KTree.node A10K2.u6820 (nat_lit 115076531) (nat_lit 9562641334) (nat_lit 0) A10K2.u6823 from rfl, totK_node, atot6820, atot6823]
  decide +kernel

theorem arows6832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6832 = true := by
  rw [show A10K2.u6832 = KTree.node A10K2.u6828 (nat_lit 115109375) (nat_lit 14004808951) (nat_lit 0) A10K2.u6831 from rfl, allE_node, arows6828, irow6832, arows6831]
  all_goals rfl

theorem atot6832 : totK PA10K2 A10K2.u6832 = [0, 1272047147352, 7330620137748, 14842373281581, 11990391046773, 3369471837464, 260838551664, 0, 0, 0] := by
  rw [show A10K2.u6832 = KTree.node A10K2.u6828 (nat_lit 115109375) (nat_lit 14004808951) (nat_lit 0) A10K2.u6831 from rfl, totK_node, atot6828, atot6831]
  decide +kernel

theorem arows6839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6839 = true := by
  rw [show A10K2.u6839 = KTree.node A10K2.u6835 (nat_lit 115157669) (nat_lit 7254936767) (nat_lit 0) A10K2.u6838 from rfl, allE_node, arows6835, irow6839, arows6838]
  all_goals rfl

theorem atot6839 : totK PA10K2 A10K2.u6839 = [0, 1472590905489, 7853913003972, 14824293023876, 11291997775657, 3090361823053, 274337859240, 7007974415, 0, 0] := by
  rw [show A10K2.u6839 = KTree.node A10K2.u6835 (nat_lit 115157669) (nat_lit 7254936767) (nat_lit 0) A10K2.u6838 from rfl, totK_node, atot6835, atot6838]
  decide +kernel

theorem arows6849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6849 = true := by
  rw [show A10K2.u6849 = KTree.node A10K2.u6845 (nat_lit 115190856) (nat_lit 12027960071) (nat_lit 0) A10K2.u6848 from rfl, allE_node, arows6845, irow6849, arows6848]
  all_goals rfl

theorem atot6849 : totK PA10K2 A10K2.u6849 = [0, 742652240717, 5513832925856, 14035866709927, 14110281439296, 4883291619345, 473222854112, 7151180950, 0, 0] := by
  rw [show A10K2.u6849 = KTree.node A10K2.u6845 (nat_lit 115190856) (nat_lit 12027960071) (nat_lit 0) A10K2.u6848 from rfl, totK_node, atot6845, atot6848]
  decide +kernel

theorem arows6856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6856 = true := by
  rw [show A10K2.u6856 = KTree.node A10K2.u6852 (nat_lit 115289820) (nat_lit 7607656934) (nat_lit 0) A10K2.u6855 from rfl, allE_node, arows6852, irow6856, arows6855]
  all_goals rfl

theorem atot6856 : totK PA10K2 A10K2.u6856 = [0, 2292362368598, 10659962382092, 16295002516175, 8905725963019, 1322045833939, 30983776799, 0, 0, 0] := by
  rw [show A10K2.u6856 = KTree.node A10K2.u6852 (nat_lit 115289820) (nat_lit 7607656934) (nat_lit 0) A10K2.u6855 from rfl, totK_node, atot6852, atot6855]
  decide +kernel

theorem arows6864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6864 = true := by
  rw [show A10K2.u6864 = KTree.node A10K2.u6860 (nat_lit 115321005) (nat_lit 5587666280) (nat_lit 0) A10K2.u6863 from rfl, allE_node, arows6860, irow6864, arows6863]
  all_goals rfl

theorem atot6864 : totK PA10K2 A10K2.u6864 = [0, 0, 2736625787133, 11914146847315, 16472978240668, 7417356857096, 852472662963, 18779342994, 0, 0] := by
  rw [show A10K2.u6864 = KTree.node A10K2.u6860 (nat_lit 115321005) (nat_lit 5587666280) (nat_lit 0) A10K2.u6863 from rfl, totK_node, atot6860, atot6863]
  decide +kernel

theorem arows6871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6871 = true := by
  rw [show A10K2.u6871 = KTree.node A10K2.u6867 (nat_lit 115350291) (nat_lit 3658223439) (nat_lit 0) A10K2.u6870 from rfl, allE_node, arows6867, irow6871, arows6870]
  all_goals rfl

theorem atot6871 : totK PA10K2 A10K2.u6871 = [0, 2231826234337, 9581816175594, 13974106105380, 8630774873973, 3367784490647, 797715412509, 54997142734, 0, 0] := by
  rw [show A10K2.u6871 = KTree.node A10K2.u6867 (nat_lit 115350291) (nat_lit 3658223439) (nat_lit 0) A10K2.u6870 from rfl, totK_node, atot6867, atot6870]
  decide +kernel

theorem arows6880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6880 = true := by
  rw [show A10K2.u6880 = KTree.node A10K2.u6876 (nat_lit 115382348) (nat_lit 10913712618) (nat_lit 0) A10K2.u6879 from rfl, allE_node, arows6876, irow6880, arows6879]
  all_goals rfl

theorem atot6880 : totK PA10K2 A10K2.u6880 = [0, 0, 3026282997132, 12307140396107, 15706502292204, 6575949831661, 905824444977, 36196801203, 0, 0] := by
  rw [show A10K2.u6880 = KTree.node A10K2.u6876 (nat_lit 115382348) (nat_lit 10913712618) (nat_lit 0) A10K2.u6879 from rfl, totK_node, atot6876, atot6879]
  decide +kernel

theorem arows6887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6887 = true := by
  rw [show A10K2.u6887 = KTree.node A10K2.u6883 (nat_lit 115493431) (nat_lit 8963760642) (nat_lit 0) A10K2.u6886 from rfl, allE_node, arows6883, irow6887, arows6886]
  all_goals rfl

theorem atot6887 : totK PA10K2 A10K2.u6887 = [0, 1318949507170, 7433887379915, 14851171982552, 11743209530078, 3010695628016, 201571720220, 0, 0, 0] := by
  rw [show A10K2.u6887 = KTree.node A10K2.u6883 (nat_lit 115493431) (nat_lit 8963760642) (nat_lit 0) A10K2.u6886 from rfl, totK_node, atot6883, atot6886]
  decide +kernel

theorem arows6895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6895 = true := by
  rw [show A10K2.u6895 = KTree.node A10K2.u6891 (nat_lit 115551672) (nat_lit 13509252260) (nat_lit 0) A10K2.u6894 from rfl, allE_node, arows6891, irow6895, arows6894]
  all_goals rfl

theorem atot6895 : totK PA10K2 A10K2.u6895 = [0, 2252464922703, 10185299310601, 15604178406818, 9261083979957, 2094744222354, 186932731686, 5976421810, 0, 0] := by
  rw [show A10K2.u6895 = KTree.node A10K2.u6891 (nat_lit 115551672) (nat_lit 13509252260) (nat_lit 0) A10K2.u6894 from rfl, totK_node, atot6891, atot6894]
  decide +kernel

theorem arows6902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6902 = true := by
  rw [show A10K2.u6902 = KTree.node A10K2.u6898 (nat_lit 115582906) (nat_lit 14684584235) (nat_lit 0) A10K2.u6901 from rfl, allE_node, arows6898, irow6902, arows6901]
  all_goals rfl

theorem atot6902 : totK PA10K2 A10K2.u6902 = [0, 0, 2576972182881, 11446253136983, 16540277946565, 8134933744804, 994919447820, 19738242144, 0, 0] := by
  rw [show A10K2.u6902 = KTree.node A10K2.u6898 (nat_lit 115582906) (nat_lit 14684584235) (nat_lit 0) A10K2.u6901 from rfl, totK_node, atot6898, atot6901]
  decide +kernel

theorem arows6914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6914 = true := by
  rw [show A10K2.u6914 = KTree.node A10K2.u6910 (nat_lit 115613127) (nat_lit 14467255561) (nat_lit 0) A10K2.u6913 from rfl, allE_node, arows6910, irow6914, arows6913]
  all_goals rfl

theorem atot6914 : totK PA10K2 A10K2.u6914 = [0, 0, 2231826234337, 10185629281096, 15558511275059, 8765758165319, 1669482784867, 91579861429, 0, 0] := by
  rw [show A10K2.u6914 = KTree.node A10K2.u6910 (nat_lit 115613127) (nat_lit 14467255561) (nat_lit 0) A10K2.u6913 from rfl, totK_node, atot6910, atot6913]
  decide +kernel

theorem arows6921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6921 = true := by
  rw [show A10K2.u6921 = KTree.node A10K2.u6917 (nat_lit 115655088) (nat_lit 14672414364) (nat_lit 0) A10K2.u6920 from rfl, allE_node, arows6917, irow6921, arows6920]
  all_goals rfl

theorem atot6921 : totK PA10K2 A10K2.u6921 = [0, 0, 759378239577, 5853645163753, 14230851403746, 13248448071686, 4193100192603, 429069091855, 7237400819, 0] := by
  rw [show A10K2.u6921 = KTree.node A10K2.u6917 (nat_lit 115655088) (nat_lit 14672414364) (nat_lit 0) A10K2.u6920 from rfl, totK_node, atot6917, atot6920]
  decide +kernel

theorem arows6929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6929 = true := by
  rw [show A10K2.u6929 = KTree.node A10K2.u6925 (nat_lit 115806108) (nat_lit 4168505398) (nat_lit 0) A10K2.u6928 from rfl, allE_node, arows6925, irow6929, arows6928]
  all_goals rfl

theorem atot6929 : totK PA10K2 A10K2.u6929 = [0, 0, 2483146556377, 10999349119730, 16154636606528, 8173037637177, 1153344863600, 31148427544, 0, 0] := by
  rw [show A10K2.u6929 = KTree.node A10K2.u6925 (nat_lit 115806108) (nat_lit 4168505398) (nat_lit 0) A10K2.u6928 from rfl, totK_node, atot6925, atot6928]
  decide +kernel

theorem arows6936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6936 = true := by
  rw [show A10K2.u6936 = KTree.node A10K2.u6932 (nat_lit 115944850) (nat_lit 15259374986) (nat_lit 0) A10K2.u6935 from rfl, allE_node, arows6932, irow6936, arows6935]
  all_goals rfl

theorem atot6936 : totK PA10K2 A10K2.u6936 = [0, 1624997771604, 7349297983575, 12789835086063, 10886002398572, 5044705385387, 1054620239475, 62368562949, 0, 0] := by
  rw [show A10K2.u6936 = KTree.node A10K2.u6932 (nat_lit 115944850) (nat_lit 15259374986) (nat_lit 0) A10K2.u6935 from rfl, totK_node, atot6932, atot6935]
  decide +kernel

theorem arows6945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6945 = true := by
  rw [show A10K2.u6945 = KTree.node A10K2.u6941 (nat_lit 115976740) (nat_lit 13394116009) (nat_lit 0) A10K2.u6944 from rfl, allE_node, arows6941, irow6945, arows6944]
  all_goals rfl

theorem atot6945 : totK PA10K2 A10K2.u6945 = [0, 613166546329, 4829213980431, 12766479102751, 14045312408407, 5824342622829, 775429605825, 31082886609, 0, 0] := by
  rw [show A10K2.u6945 = KTree.node A10K2.u6941 (nat_lit 115976740) (nat_lit 13394116009) (nat_lit 0) A10K2.u6944 from rfl, totK_node, atot6941, atot6944]
  decide +kernel

theorem arows6952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6952 = true := by
  rw [show A10K2.u6952 = KTree.node A10K2.u6948 (nat_lit 116013214) (nat_lit 12738906020) (nat_lit 0) A10K2.u6951 from rfl, allE_node, arows6948, irow6952, arows6951]
  all_goals rfl

theorem atot6952 : totK PA10K2 A10K2.u6952 = [0, 1323934157412, 7722694552090, 15175853915213, 11638925768782, 3118396166653, 282881940870, 5885702948, 0, 0] := by
  rw [show A10K2.u6952 = KTree.node A10K2.u6948 (nat_lit 116013214) (nat_lit 12738906020) (nat_lit 0) A10K2.u6951 from rfl, totK_node, atot6948, atot6951]
  decide +kernel

theorem arows6960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6960 = true := by
  rw [show A10K2.u6960 = KTree.node A10K2.u6956 (nat_lit 116073645) (nat_lit 6298462711) (nat_lit 0) A10K2.u6959 from rfl, allE_node, arows6956, irow6960, arows6959]
  all_goals rfl

theorem atot6960 : totK PA10K2 A10K2.u6960 = [0, 1997296793756, 9112407295761, 14898339934001, 10220977275049, 2743845673954, 272303882698, 6354482628, 0, 0] := by
  rw [show A10K2.u6960 = KTree.node A10K2.u6956 (nat_lit 116073645) (nat_lit 6298462711) (nat_lit 0) A10K2.u6959 from rfl, totK_node, atot6956, atot6959]
  decide +kernel

theorem arows6967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6967 = true := by
  rw [show A10K2.u6967 = KTree.node A10K2.u6963 (nat_lit 116101900) (nat_lit 9486903530) (nat_lit 0) A10K2.u6966 from rfl, allE_node, arows6963, irow6967, arows6966]
  all_goals rfl

theorem atot6967 : totK PA10K2 A10K2.u6967 = [0, 244406495887, 3892046766869, 12891576723412, 15470821709116, 6586447369215, 740504552943, 13679205470, 0, 0] := by
  rw [show A10K2.u6967 = KTree.node A10K2.u6963 (nat_lit 116101900) (nat_lit 9486903530) (nat_lit 0) A10K2.u6966 from rfl, totK_node, atot6963, atot6966]
  decide +kernel

theorem arows6977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6977 = true := by
  rw [show A10K2.u6977 = KTree.node A10K2.u6973 (nat_lit 116207266) (nat_lit 14388455778) (nat_lit 0) A10K2.u6976 from rfl, allE_node, arows6973, irow6977, arows6976]
  all_goals rfl

theorem atot6977 : totK PA10K2 A10K2.u6977 = [0, 0, 2063854968044, 9712043663463, 15615411369633, 9443656136119, 1841446316074, 98635968377, 0, 0] := by
  rw [show A10K2.u6977 = KTree.node A10K2.u6973 (nat_lit 116207266) (nat_lit 14388455778) (nat_lit 0) A10K2.u6976 from rfl, totK_node, atot6973, atot6976]
  decide +kernel

theorem arows6984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6984 = true := by
  rw [show A10K2.u6984 = KTree.node A10K2.u6980 (nat_lit 116239801) (nat_lit 6471814591) (nat_lit 0) A10K2.u6983 from rfl, allE_node, arows6980, irow6984, arows6983]
  all_goals rfl

theorem atot6984 : totK PA10K2 A10K2.u6984 = [0, 0, 801526633583, 5693613448615, 14169912542183, 13678659528969, 4408514136464, 433293682688, 7380853412, 0] := by
  rw [show A10K2.u6984 = KTree.node A10K2.u6980 (nat_lit 116239801) (nat_lit 6471814591) (nat_lit 0) A10K2.u6983 from rfl, totK_node, atot6980, atot6983]
  decide +kernel

theorem arows6992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6992 = true := by
  rw [show A10K2.u6992 = KTree.node A10K2.u6988 (nat_lit 116330017) (nat_lit 9307298794) (nat_lit 0) A10K2.u6991 from rfl, allE_node, arows6988, irow6992, arows6991]
  all_goals rfl

theorem atot6992 : totK PA10K2 A10K2.u6992 = [0, 0, 2462488540677, 11223377857668, 16395430957934, 8080034691030, 1092079580840, 25772320064, 0, 0] := by
  rw [show A10K2.u6992 = KTree.node A10K2.u6988 (nat_lit 116330017) (nat_lit 9307298794) (nat_lit 0) A10K2.u6991 from rfl, totK_node, atot6988, atot6991]
  decide +kernel

theorem arows6999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6999 = true := by
  rw [show A10K2.u6999 = KTree.node A10K2.u6995 (nat_lit 116917138) (nat_lit 10299633310) (nat_lit 0) A10K2.u6998 from rfl, allE_node, arows6995, irow6999, arows6998]
  all_goals rfl

theorem atot6999 : totK PA10K2 A10K2.u6999 = [0, 1427351586688, 7060564692249, 12906751215958, 11150725059240, 5216354061529, 1061556013649, 62382159641, 0, 0] := by
  rw [show A10K2.u6999 = KTree.node A10K2.u6995 (nat_lit 116917138) (nat_lit 10299633310) (nat_lit 0) A10K2.u6998 from rfl, totK_node, atot6995, atot6998]
  decide +kernel

theorem arows7008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7008 = true := by
  rw [show A10K2.u7008 = KTree.node A10K2.u7004 (nat_lit 116951560) (nat_lit 14167382902) (nat_lit 0) A10K2.u7007 from rfl, allE_node, arows7004, irow7008, arows7007]
  all_goals rfl

theorem atot7008 : totK PA10K2 A10K2.u7008 = [0, 653619017713, 5058946390692, 13332750818364, 14093042701374, 5365095413929, 614430480872, 12477124820, 0, 0] := by
  rw [show A10K2.u7008 = KTree.node A10K2.u7004 (nat_lit 116951560) (nat_lit 14167382902) (nat_lit 0) A10K2.u7007 from rfl, totK_node, atot7004, atot7007]
  decide +kernel

theorem arows7015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7015 = true := by
  rw [show A10K2.u7015 = KTree.node A10K2.u7011 (nat_lit 116997622) (nat_lit 16825448452) (nat_lit 0) A10K2.u7014 from rfl, allE_node, arows7011, irow7015, arows7014]
  all_goals rfl

theorem atot7015 : totK PA10K2 A10K2.u7015 = [0, 2088351472436, 9858760888251, 15816107452182, 9738107540777, 2017880972786, 102909406710, 0, 0, 0] := by
  rw [show A10K2.u7015 = KTree.node A10K2.u7011 (nat_lit 116997622) (nat_lit 16825448452) (nat_lit 0) A10K2.u7014 from rfl, totK_node, atot7011, atot7014]
  decide +kernel

theorem arows7023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7023 = true := by
  rw [show A10K2.u7023 = KTree.node A10K2.u7019 (nat_lit 117032669) (nat_lit 5476737718) (nat_lit 0) A10K2.u7022 from rfl, allE_node, arows7019, irow7023, arows7022]
  all_goals rfl

theorem atot7023 : totK PA10K2 A10K2.u7023 = [0, 762038499923, 4997713667206, 12633485881187, 14098458616100, 5880703848279, 674866296433, 12696458652, 0, 0] := by
  rw [show A10K2.u7023 = KTree.node A10K2.u7019 (nat_lit 117032669) (nat_lit 5476737718) (nat_lit 0) A10K2.u7022 from rfl, totK_node, atot7019, atot7022]
  decide +kernel

theorem arows7030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7030 = true := by
  rw [show A10K2.u7030 = KTree.node A10K2.u7026 (nat_lit 117128350) (nat_lit 15173479105) (nat_lit 0) A10K2.u7029 from rfl, allE_node, arows7026, irow7030, arows7029]
  all_goals rfl

theorem atot7030 : totK PA10K2 A10K2.u7030 = [0, 1662197905889, 8909798071569, 15990251951442, 10643715937650, 2203590623451, 98251902764, 0, 0, 0] := by
  rw [show A10K2.u7030 = KTree.node A10K2.u7026 (nat_lit 117128350) (nat_lit 15173479105) (nat_lit 0) A10K2.u7029 from rfl, totK_node, atot7026, atot7029]
  decide +kernel

theorem arows7041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7041 = true := by
  rw [show A10K2.u7041 = KTree.node A10K2.u7037 (nat_lit 117159074) (nat_lit 14523975480) (nat_lit 0) A10K2.u7040 from rfl, allE_node, arows7037, irow7041, arows7040]
  all_goals rfl

theorem atot7041 : totK PA10K2 A10K2.u7041 = [0, 0, 2234290110965, 10741682726428, 16539360725460, 8649785571685, 1133820771755, 26176060751, 0, 0] := by
  rw [show A10K2.u7041 = KTree.node A10K2.u7037 (nat_lit 117159074) (nat_lit 14523975480) (nat_lit 0) A10K2.u7040 from rfl, totK_node, atot7037, atot7040]
  decide +kernel

theorem arows7048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7048 = true := by
  rw [show A10K2.u7048 = KTree.node A10K2.u7044 (nat_lit 117196871) (nat_lit 6275057308) (nat_lit 0) A10K2.u7047 from rfl, allE_node, arows7044, irow7048, arows7047]
  all_goals rfl

theorem atot7048 : totK PA10K2 A10K2.u7048 = [0, 0, 2074028134644, 9654742449678, 15511269336787, 9827335073175, 2128757791961, 123714960702, 0, 0] := by
  rw [show A10K2.u7048 = KTree.node A10K2.u7044 (nat_lit 117196871) (nat_lit 6275057308) (nat_lit 0) A10K2.u7047 from rfl, totK_node, atot7044, atot7047]
  decide +kernel

theorem arows7056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7056 = true := by
  rw [show A10K2.u7056 = KTree.node A10K2.u7052 (nat_lit 117238884) (nat_lit 7799616001) (nat_lit 0) A10K2.u7055 from rfl, allE_node, arows7052, irow7056, arows7055]
  all_goals rfl

theorem atot7056 : totK PA10K2 A10K2.u7056 = [0, 0, 1081840141366, 6599550208267, 14449104451243, 12721724911460, 3759255473868, 324666081941, 6725424603, 0] := by
  rw [show A10K2.u7056 = KTree.node A10K2.u7052 (nat_lit 117238884) (nat_lit 7799616001) (nat_lit 0) A10K2.u7055 from rfl, totK_node, atot7052, atot7055]
  decide +kernel

theorem arows7063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7063 = true := by
  rw [show A10K2.u7063 = KTree.node A10K2.u7059 (nat_lit 117286052) (nat_lit 13127005630) (nat_lit 0) A10K2.u7062 from rfl, allE_node, arows7059, irow7063, arows7062]
  all_goals rfl

theorem atot7063 : totK PA10K2 A10K2.u7063 = [0, 0, 999573930879, 6784328339186, 14876243430164, 12880686641960, 3835536244382, 335250020912, 6860445330, 0] := by
  rw [show A10K2.u7063 = KTree.node A10K2.u7059 (nat_lit 117286052) (nat_lit 13127005630) (nat_lit 0) A10K2.u7062 from rfl, totK_node, atot7059, atot7062]
  decide +kernel

theorem arows7072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7072 = true := by
  rw [show A10K2.u7072 = KTree.node A10K2.u7068 (nat_lit 117385900) (nat_lit 9592721117) (nat_lit 0) A10K2.u7071 from rfl, allE_node, arows7068, irow7072, arows7071]
  all_goals rfl

theorem atot7072 : totK PA10K2 A10K2.u7072 = [0, 0, 2407789929719, 10676090982382, 15849277467587, 8778285948877, 1490616551060, 74045117265, 0, 0] := by
  rw [show A10K2.u7072 = KTree.node A10K2.u7068 (nat_lit 117385900) (nat_lit 9592721117) (nat_lit 0) A10K2.u7071 from rfl, totK_node, atot7068, atot7071]
  decide +kernel

theorem arows7079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7079 = true := by
  rw [show A10K2.u7079 = KTree.node A10K2.u7075 (nat_lit 117417298) (nat_lit 15123806206) (nat_lit 0) A10K2.u7078 from rfl, allE_node, arows7075, irow7079, arows7078]
  all_goals rfl

theorem atot7079 : totK PA10K2 A10K2.u7079 = [0, 0, 0, 2992680621676, 12515165315253, 16340562800073, 6616080670137, 706032126232, 12758098799, 0] := by
  rw [show A10K2.u7079 = KTree.node A10K2.u7075 (nat_lit 117417298) (nat_lit 15123806206) (nat_lit 0) A10K2.u7078 from rfl, totK_node, atot7075, atot7078]
  decide +kernel

theorem arows7087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7087 = true := by
  rw [show A10K2.u7087 = KTree.node A10K2.u7083 (nat_lit 117445512) (nat_lit 14141392688) (nat_lit 0) A10K2.u7086 from rfl, allE_node, arows7083, irow7087, arows7086]
  all_goals rfl

theorem atot7087 : totK PA10K2 A10K2.u7087 = [0, 2029155319813, 8705610476949, 12356826860946, 6999410501179, 3936993361600, 3187341418643, 910141810368, 61018386929, 0] := by
  rw [show A10K2.u7087 = KTree.node A10K2.u7083 (nat_lit 117445512) (nat_lit 14141392688) (nat_lit 0) A10K2.u7086 from rfl, totK_node, atot7083, atot7086]
  decide +kernel

theorem arows7094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7094 = true := by
  rw [show A10K2.u7094 = KTree.node A10K2.u7090 (nat_lit 117477249) (nat_lit 9900015714) (nat_lit 0) A10K2.u7093 from rfl, allE_node, arows7090, irow7094, arows7093]
  all_goals rfl

theorem atot7094 : totK PA10K2 A10K2.u7094 = [0, 309893393367, 3908859679521, 12383468981482, 14640905536829, 6099034064548, 874384417201, 36196801203, 0, 0] := by
  rw [show A10K2.u7094 = KTree.node A10K2.u7090 (nat_lit 117477249) (nat_lit 9900015714) (nat_lit 0) A10K2.u7093 from rfl, totK_node, atot7090, atot7093]
  decide +kernel

theorem arows7104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7104 = true := by
  rw [show A10K2.u7104 = KTree.node A10K2.u7100 (nat_lit 117578519) (nat_lit 1268508520) (nat_lit 0) A10K2.u7103 from rfl, allE_node, arows7100, irow7104, arows7103]
  all_goals rfl

theorem atot7104 : totK PA10K2 A10K2.u7104 = [0, 1789785501203, 9062883542156, 15474073927985, 9978722948270, 2140821483760, 120531872305, 0, 0, 0] := by
  rw [show A10K2.u7104 = KTree.node A10K2.u7100 (nat_lit 117578519) (nat_lit 1268508520) (nat_lit 0) A10K2.u7103 from rfl, totK_node, atot7100, atot7103]
  decide +kernel

theorem arows7111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7111 = true := by
  rw [show A10K2.u7111 = KTree.node A10K2.u7107 (nat_lit 117627206) (nat_lit 7254210050) (nat_lit 0) A10K2.u7110 from rfl, allE_node, arows7107, irow7111, arows7110]
  all_goals rfl

theorem atot7111 : totK PA10K2 A10K2.u7111 = [0, 1322837559556, 7073851156549, 14321557536015, 12255147880814, 3499621829949, 302046875224, 6354482628, 0, 0] := by
  rw [show A10K2.u7111 = KTree.node A10K2.u7107 (nat_lit 117627206) (nat_lit 7254210050) (nat_lit 0) A10K2.u7110 from rfl, totK_node, atot7107, atot7110]
  decide +kernel

theorem arows7119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7119 = true := by
  rw [show A10K2.u7119 = KTree.node A10K2.u7115 (nat_lit 117669416) (nat_lit 11782639116) (nat_lit 0) A10K2.u7118 from rfl, allE_node, arows7115, irow7119, arows7118]
  all_goals rfl

theorem atot7119 : totK PA10K2 A10K2.u7119 = [0, 845700278790, 5975843952697, 14369485775381, 13861616767230, 4801974629433, 469869803090, 6904928264, 0, 0] := by
  rw [show A10K2.u7119 = KTree.node A10K2.u7115 (nat_lit 117669416) (nat_lit 11782639116) (nat_lit 0) A10K2.u7118 from rfl, totK_node, atot7115, atot7118]
  decide +kernel

theorem arows7126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7126 = true := by
  rw [show A10K2.u7126 = KTree.node A10K2.u7122 (nat_lit 117702554) (nat_lit 13820892800) (nat_lit 0) A10K2.u7125 from rfl, allE_node, arows7122, irow7126, arows7125]
  all_goals rfl

theorem atot7126 : totK PA10K2 A10K2.u7126 = [0, 0, 2123087212281, 9820367777528, 15706745035925, 9688362386223, 1905687888431, 98988825444, 0, 0] := by
  rw [show A10K2.u7126 = KTree.node A10K2.u7122 (nat_lit 117702554) (nat_lit 13820892800) (nat_lit 0) A10K2.u7125 from rfl, totK_node, atot7122, atot7125]
  decide +kernel

theorem arows7135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7135 = true := by
  rw [show A10K2.u7135 = KTree.node A10K2.u7131 (nat_lit 117734414) (nat_lit 14689662443) (nat_lit 0) A10K2.u7134 from rfl, allE_node, arows7131, irow7135, arows7134]
  all_goals rfl

theorem atot7135 : totK PA10K2 A10K2.u7135 = [0, 0, 1056700981572, 6630957960544, 14014622818635, 11741450629514, 4085112100297, 616395076921, 30605747850, 0] := by
  rw [show A10K2.u7135 = KTree.node A10K2.u7131 (nat_lit 117734414) (nat_lit 14689662443) (nat_lit 0) A10K2.u7134 from rfl, totK_node, atot7131, atot7134]
  decide +kernel

theorem arows7142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7142 = true := by
  rw [show A10K2.u7142 = KTree.node A10K2.u7138 (nat_lit 117836000) (nat_lit 9009101019) (nat_lit 0) A10K2.u7141 from rfl, allE_node, arows7138, irow7142, arows7141]
  all_goals rfl

theorem atot7142 : totK PA10K2 A10K2.u7142 = [0, 0, 1574207055282, 7734965274204, 14122509440510, 10927231957197, 3149547131715, 308509062959, 5528811039, 0] := by
  rw [show A10K2.u7142 = KTree.node A10K2.u7138 (nat_lit 117836000) (nat_lit 9009101019) (nat_lit 0) A10K2.u7141 from rfl, totK_node, atot7138, atot7141]
  decide +kernel

theorem arows7150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7150 = true := by
  rw [show A10K2.u7150 = KTree.node A10K2.u7146 (nat_lit 117883685) (nat_lit 7382826692) (nat_lit 0) A10K2.u7149 from rfl, allE_node, arows7146, irow7150, arows7149]
  all_goals rfl

theorem atot7150 : totK PA10K2 A10K2.u7150 = [0, 0, 1021763350823, 6734719180932, 14546545518954, 11835978013346, 3157023351195, 294131456219, 5676195732, 0] := by
  rw [show A10K2.u7150 = KTree.node A10K2.u7146 (nat_lit 117883685) (nat_lit 7382826692) (nat_lit 0) A10K2.u7149 from rfl, totK_node, atot7146, atot7149]
  decide +kernel

theorem arows7157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7157 = true := by
  rw [show A10K2.u7157 = KTree.node A10K2.u7153 (nat_lit 117927815) (nat_lit 14658428996) (nat_lit 0) A10K2.u7156 from rfl, allE_node, arows7153, irow7157, arows7156]
  all_goals rfl

theorem atot7157 : totK PA10K2 A10K2.u7157 = [0, 839403861465, 4734740216844, 11192131369743, 13709510406809, 7942658875195, 1575176584831, 74774849751, 0, 0] := by
  rw [show A10K2.u7157 = KTree.node A10K2.u7153 (nat_lit 117927815) (nat_lit 14658428996) (nat_lit 0) A10K2.u7156 from rfl, totK_node, atot7153, atot7156]
  decide +kernel

theorem arows7171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7171 = true := by
  rw [show A10K2.u7171 = KTree.node A10K2.u7167 (nat_lit 118514582) (nat_lit 15346058908) (nat_lit 0) A10K2.u7170 from rfl, allE_node, arows7167, irow7171, arows7170]
  all_goals rfl

theorem atot7171 : totK PA10K2 A10K2.u7171 = [0, 1343077793455, 7594534658641, 14853883800740, 11510198247714, 3171671959631, 349722426505, 20060612110, 0, 0] := by
  rw [show A10K2.u7171 = KTree.node A10K2.u7167 (nat_lit 118514582) (nat_lit 15346058908) (nat_lit 0) A10K2.u7170 from rfl, totK_node, atot7167, atot7170]
  decide +kernel

theorem arows7178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7178 = true := by
  rw [show A10K2.u7178 = KTree.node A10K2.u7174 (nat_lit 118549893) (nat_lit 4084932589) (nat_lit 0) A10K2.u7177 from rfl, allE_node, arows7174, irow7178, arows7177]
  all_goals rfl

theorem atot7178 : totK PA10K2 A10K2.u7178 = [0, 1219014644614, 6331196825172, 13056735633340, 12445091768278, 4760369096392, 603499972451, 16136189093, 0, 0] := by
  rw [show A10K2.u7178 = KTree.node A10K2.u7174 (nat_lit 118549893) (nat_lit 4084932589) (nat_lit 0) A10K2.u7177 from rfl, totK_node, atot7174, atot7177]
  decide +kernel

theorem arows7186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7186 = true := by
  rw [show A10K2.u7186 = KTree.node A10K2.u7182 (nat_lit 118643208) (nat_lit 12461233422) (nat_lit 0) A10K2.u7185 from rfl, allE_node, arows7182, irow7186, arows7185]
  all_goals rfl

theorem atot7186 : totK PA10K2 A10K2.u7186 = [0, 928536070374, 6941281625446, 15357120594153, 11961046864401, 2700476228956, 159644730938, 0, 0, 0] := by
  rw [show A10K2.u7186 = KTree.node A10K2.u7182 (nat_lit 118643208) (nat_lit 12461233422) (nat_lit 0) A10K2.u7185 from rfl, totK_node, atot7182, atot7185]
  decide +kernel

theorem arows7193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7193 = true := by
  rw [show A10K2.u7193 = KTree.node A10K2.u7189 (nat_lit 118757651) (nat_lit 9362211444) (nat_lit 0) A10K2.u7192 from rfl, allE_node, arows7189, irow7193, arows7192]
  all_goals rfl

theorem atot7193 : totK PA10K2 A10K2.u7193 = [0, 0, 2313782801794, 10907600746085, 16053359286892, 7659411082648, 1132181165950, 43527332123, 0, 0] := by
  rw [show A10K2.u7193 = KTree.node A10K2.u7189 (nat_lit 118757651) (nat_lit 9362211444) (nat_lit 0) A10K2.u7192 from rfl, totK_node, atot7189, atot7192]
  decide +kernel

theorem arows7202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7202 = true := by
  rw [show A10K2.u7202 = KTree.node A10K2.u7198 (nat_lit 118891811) (nat_lit 10336289781) (nat_lit 0) A10K2.u7201 from rfl, allE_node, arows7198, irow7202, arows7201]
  all_goals rfl

theorem atot7202 : totK PA10K2 A10K2.u7202 = [0, 0, 2144943767679, 10497198477911, 16298729217968, 8149159651776, 1148760121239, 42962447115, 0, 0] := by
  rw [show A10K2.u7202 = KTree.node A10K2.u7198 (nat_lit 118891811) (nat_lit 10336289781) (nat_lit 0) A10K2.u7201 from rfl, totK_node, atot7198, atot7201]
  decide +kernel

theorem arows7209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7209 = true := by
  rw [show A10K2.u7209 = KTree.node A10K2.u7205 (nat_lit 118934177) (nat_lit 7859361199) (nat_lit 0) A10K2.u7208 from rfl, allE_node, arows7205, irow7209, arows7208]
  all_goals rfl

theorem atot7209 : totK PA10K2 A10K2.u7209 = [0, 835923233680, 3743102169442, 7961715823634, 12015637649671, 9853016935135, 2823407352823, 269843535820, 6354482628, 0] := by
  rw [show A10K2.u7209 = KTree.node A10K2.u7205 (nat_lit 118934177) (nat_lit 7859361199) (nat_lit 0) A10K2.u7208 from rfl, totK_node, atot7205, atot7208]
  decide +kernel

theorem arows7217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7217 = true := by
  rw [show A10K2.u7217 = KTree.node A10K2.u7213 (nat_lit 119042572) (nat_lit 10619496358) (nat_lit 0) A10K2.u7216 from rfl, allE_node, arows7213, irow7217, arows7216]
  all_goals rfl

theorem atot7217 : totK PA10K2 A10K2.u7217 = [0, 1341052302012, 7216262627320, 14030141070178, 11658469666473, 4103692169150, 617667972416, 30650496230, 0, 0] := by
  rw [show A10K2.u7217 = KTree.node A10K2.u7213 (nat_lit 119042572) (nat_lit 10619496358) (nat_lit 0) A10K2.u7216 from rfl, totK_node, atot7213, atot7216]
  decide +kernel

theorem arows7224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7224 = true := by
  rw [show A10K2.u7224 = KTree.node A10K2.u7220 (nat_lit 119088804) (nat_lit 13034769765) (nat_lit 0) A10K2.u7223 from rfl, allE_node, arows7220, irow7224, arows7223]
  all_goals rfl

theorem atot7224 : totK PA10K2 A10K2.u7224 = [0, 1606735580082, 8024096164092, 14706642416892, 11759747739382, 3535686538629, 336209504251, 5546304973, 0, 0] := by
  rw [show A10K2.u7224 = KTree.node A10K2.u7220 (nat_lit 119088804) (nat_lit 13034769765) (nat_lit 0) A10K2.u7223 from rfl, totK_node, atot7220, atot7223]
  decide +kernel

theorem arows7234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7234 = true := by
  rw [show A10K2.u7234 = KTree.node A10K2.u7230 (nat_lit 119126824) (nat_lit 8025585773) (nat_lit 0) A10K2.u7233 from rfl, allE_node, arows7230, irow7234, arows7233]
  all_goals rfl

theorem atot7234 : totK PA10K2 A10K2.u7234 = [0, 777824669607, 5577417041678, 13812969189653, 14077246367205, 5356533659949, 622883587492, 13576218110, 0, 0] := by
  rw [show A10K2.u7234 = KTree.node A10K2.u7230 (nat_lit 119126824) (nat_lit 8025585773) (nat_lit 0) A10K2.u7233 from rfl, totK_node, atot7230, atot7233]
  decide +kernel

theorem arows7241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7241 = true := by
  rw [show A10K2.u7241 = KTree.node A10K2.u7237 (nat_lit 119236055) (nat_lit 14300367555) (nat_lit 0) A10K2.u7240 from rfl, allE_node, arows7237, irow7241, arows7240]
  all_goals rfl

theorem atot7241 : totK PA10K2 A10K2.u7241 = [0, 1568941691954, 8591939250458, 16063418652146, 11313404529386, 2452280335019, 123335405801, 0, 0, 0] := by
  rw [show A10K2.u7241 = KTree.node A10K2.u7237 (nat_lit 119236055) (nat_lit 14300367555) (nat_lit 0) A10K2.u7240 from rfl, totK_node, atot7237, atot7240]
  decide +kernel

theorem arows7249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7249 = true := by
  rw [show A10K2.u7249 = KTree.node A10K2.u7245 (nat_lit 119267911) (nat_lit 9934066887) (nat_lit 0) A10K2.u7248 from rfl, allE_node, arows7245, irow7249, arows7248]
  all_goals rfl

theorem atot7249 : totK PA10K2 A10K2.u7249 = [0, 0, 2106711735542, 10121073195936, 16213318703987, 9533711108206, 1682875436017, 75062079822, 0, 0] := by
  rw [show A10K2.u7249 = KTree.node A10K2.u7245 (nat_lit 119267911) (nat_lit 9934066887) (nat_lit 0) A10K2.u7248 from rfl, totK_node, atot7245, atot7248]
  decide +kernel

theorem arows7256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7256 = true := by
  rw [show A10K2.u7256 = KTree.node A10K2.u7252 (nat_lit 119300108) (nat_lit 10934062318) (nat_lit 0) A10K2.u7255 from rfl, allE_node, arows7252, irow7256, arows7255]
  all_goals rfl

theorem atot7256 : totK PA10K2 A10K2.u7256 = [0, 0, 1636953463023, 8789004025188, 15821458238004, 10514395163118, 2269407674718, 124412133180, 0, 0] := by
  rw [show A10K2.u7256 = KTree.node A10K2.u7252 (nat_lit 119300108) (nat_lit 10934062318) (nat_lit 0) A10K2.u7255 from rfl, totK_node, atot7252, atot7255]
  decide +kernel

theorem arows7265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7265 = true := by
  rw [show A10K2.u7265 = KTree.node A10K2.u7261 (nat_lit 119336120) (nat_lit 11635974843) (nat_lit 0) A10K2.u7264 from rfl, allE_node, arows7261, irow7265, arows7264]
  all_goals rfl

theorem atot7265 : totK PA10K2 A10K2.u7265 = [0, 0, 1284111989839, 6976070433650, 14296520906863, 12667560091857, 4010725597178, 396626142895, 7007974415, 0] := by
  rw [show A10K2.u7265 = KTree.node A10K2.u7261 (nat_lit 119336120) (nat_lit 11635974843) (nat_lit 0) A10K2.u7264 from rfl, totK_node, atot7261, atot7264]
  decide +kernel

theorem arows7272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7272 = true := by
  rw [show A10K2.u7272 = KTree.node A10K2.u7268 (nat_lit 119387301) (nat_lit 6845936224) (nat_lit 0) A10K2.u7271 from rfl, allE_node, arows7268, irow7272, arows7271]
  all_goals rfl

theorem atot7272 : totK PA10K2 A10K2.u7272 = [0, 0, 1098450641108, 6690678748359, 14566375197639, 13341603466525, 4349881717361, 392702943265, 7151180950, 0] := by
  rw [show A10K2.u7272 = KTree.node A10K2.u7268 (nat_lit 119387301) (nat_lit 6845936224) (nat_lit 0) A10K2.u7271 from rfl, totK_node, atot7268, atot7271]
  decide +kernel

theorem arows7280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7280 = true := by
  rw [show A10K2.u7280 = KTree.node A10K2.u7276 (nat_lit 119497266) (nat_lit 10171640832) (nat_lit 0) A10K2.u7279 from rfl, allE_node, arows7276, irow7280, arows7279]
  all_goals rfl

theorem atot7280 : totK PA10K2 A10K2.u7280 = [0, 0, 1567451424792, 8590833699235, 16075857774716, 11340453941362, 2316535288156, 99041919305, 0, 0] := by
  rw [show A10K2.u7280 = KTree.node A10K2.u7276 (nat_lit 119497266) (nat_lit 10171640832) (nat_lit 0) A10K2.u7279 from rfl, totK_node, atot7276, atot7279]
  decide +kernel

theorem arows7287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7287 = true := by
  rw [show A10K2.u7287 = KTree.node A10K2.u7283 (nat_lit 119529768) (nat_lit 11799795512) (nat_lit 0) A10K2.u7286 from rfl, allE_node, arows7283, irow7287, arows7286]
  all_goals rfl

theorem atot7287 : totK PA10K2 A10K2.u7287 = [0, 0, 428122261071, 3232006027879, 10499169429881, 15252636360211, 8672395222232, 1545321837270, 73776485728, 0] := by
  rw [show A10K2.u7287 = KTree.node A10K2.u7283 (nat_lit 119529768) (nat_lit 11799795512) (nat_lit 0) A10K2.u7286 from rfl, totK_node, atot7283, atot7286]
  decide +kernel

theorem arows7298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7298 = true := by
  rw [show A10K2.u7298 = KTree.node A10K2.u7294 (nat_lit 119558404) (nat_lit 13036095526) (nat_lit 0) A10K2.u7297 from rfl, allE_node, arows7294, irow7298, arows7297]
  all_goals rfl

theorem atot7298 : totK PA10K2 A10K2.u7298 = [0, 0, 1910926452109, 9554800066852, 15758463012703, 9482006730408, 1830309077786, 84584600413, 0, 0] := by
  rw [show A10K2.u7298 = KTree.node A10K2.u7294 (nat_lit 119558404) (nat_lit 13036095526) (nat_lit 0) A10K2.u7297 from rfl, totK_node, atot7294, atot7297]
  decide +kernel

theorem arows7305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7305 = true := by
  rw [show A10K2.u7305 = KTree.node A10K2.u7301 (nat_lit 119589010) (nat_lit 9561354774) (nat_lit 0) A10K2.u7304 from rfl, allE_node, arows7301, irow7305, arows7304]
  all_goals rfl

theorem atot7305 : totK PA10K2 A10K2.u7305 = [0, 0, 576996404534, 4366606196845, 12084465786540, 14018032561583, 5977095324491, 873171110313, 36196801203, 0] := by
  rw [show A10K2.u7305 = KTree.node A10K2.u7301 (nat_lit 119589010) (nat_lit 9561354774) (nat_lit 0) A10K2.u7304 from rfl, totK_node, atot7301, atot7304]
  decide +kernel

theorem arows7313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7313 = true := by
  rw [show A10K2.u7313 = KTree.node A10K2.u7309 (nat_lit 119687681) (nat_lit 10399100954) (nat_lit 0) A10K2.u7312 from rfl, allE_node, arows7309, irow7313, arows7312]
  all_goals rfl

theorem atot7313 : totK PA10K2 A10K2.u7313 = [0, 0, 1212789096669, 7679603284949, 15670169681116, 11252603606276, 2175747280569, 113091996295, 0, 0] := by
  rw [show A10K2.u7313 = KTree.node A10K2.u7309 (nat_lit 119687681) (nat_lit 10399100954) (nat_lit 0) A10K2.u7312 from rfl, totK_node, atot7309, atot7312]
  decide +kernel

theorem arows7320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7320 = true := by
  rw [show A10K2.u7320 = KTree.node A10K2.u7316 (nat_lit 119740686) (nat_lit 9059311355) (nat_lit 0) A10K2.u7319 from rfl, allE_node, arows7316, irow7320, arows7319]
  all_goals rfl

theorem atot7320 : totK PA10K2 A10K2.u7320 = [0, 0, 2168537838346, 9574678060822, 15064768330190, 9911185513581, 2479060474530, 237630170052, 5976421810, 0] := by
  rw [show A10K2.u7320 = KTree.node A10K2.u7316 (nat_lit 119740686) (nat_lit 9059311355) (nat_lit 0) A10K2.u7319 from rfl, totK_node, atot7316, atot7319]
  decide +kernel

theorem arows7329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7329 = true := by
  rw [show A10K2.u7329 = KTree.node A10K2.u7325 (nat_lit 119773508) (nat_lit 12591843308) (nat_lit 0) A10K2.u7328 from rfl, allE_node, arows7325, irow7329, arows7328]
  all_goals rfl

theorem atot7329 : totK PA10K2 A10K2.u7329 = [0, 0, 0, 3009499144564, 12618707048085, 16500742364703, 7083853343988, 779362234097, 12971886742, 0] := by
  rw [show A10K2.u7329 = KTree.node A10K2.u7325 (nat_lit 119773508) (nat_lit 12591843308) (nat_lit 0) A10K2.u7328 from rfl, totK_node, atot7325, atot7328]
  decide +kernel

theorem arows7336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7336 = true := by
  rw [show A10K2.u7336 = KTree.node A10K2.u7332 (nat_lit 119816994) (nat_lit 10545891280) (nat_lit 0) A10K2.u7335 from rfl, allE_node, arows7332, irow7336, arows7335]
  all_goals rfl

theorem atot7336 : totK PA10K2 A10K2.u7336 = [0, 0, 0, 2321938910770, 10458090279896, 15654416522089, 8337346751042, 1511213905725, 71893631707, 0] := by
  rw [show A10K2.u7336 = KTree.node A10K2.u7332 (nat_lit 119816994) (nat_lit 10545891280) (nat_lit 0) A10K2.u7335 from rfl, totK_node, atot7332, atot7335]
  decide +kernel

theorem arows7344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7344 = true := by
  rw [show A10K2.u7344 = KTree.node A10K2.u7340 (nat_lit 119851076) (nat_lit 11710074203) (nat_lit 0) A10K2.u7343 from rfl, allE_node, arows7340, irow7344, arows7343]
  all_goals rfl

theorem atot7344 : totK PA10K2 A10K2.u7344 = [0, 0, 0, 789704378163, 5903213764629, 14239190998371, 12765359514129, 4074945801423, 433777954251, 7903172220] := by
  rw [show A10K2.u7344 = KTree.node A10K2.u7340 (nat_lit 119851076) (nat_lit 11710074203) (nat_lit 0) A10K2.u7343 from rfl, totK_node, atot7340, atot7343]
  decide +kernel

theorem arows7351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7351 = true := by
  rw [show A10K2.u7351 = KTree.node A10K2.u7347 (nat_lit 119998478) (nat_lit 12631121230) (nat_lit 0) A10K2.u7350 from rfl, allE_node, arows7347, irow7351, arows7350]
  all_goals rfl

theorem atot7351 : totK PA10K2 A10K2.u7351 = [0, 0, 0, 2973443857199, 12168576195098, 16043733083736, 6876160176340, 844912427244, 25175756574, 0] := by
  rw [show A10K2.u7351 = KTree.node A10K2.u7347 (nat_lit 119998478) (nat_lit 12631121230) (nat_lit 0) A10K2.u7350 from rfl, totK_node, atot7347, atot7350]
  decide +kernel

theorem arows7361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7361 = true := by
  rw [show A10K2.u7361 = KTree.node A10K2.u7357 (nat_lit 120590952) (nat_lit 12014236270) (nat_lit 0) A10K2.u7360 from rfl, allE_node, arows7357, irow7361, arows7360]
  all_goals rfl

theorem atot7361 : totK PA10K2 A10K2.u7361 = [0, 0, 1885501620505, 8610854098484, 13911649730528, 9843747396410, 3742823563608, 670000940498, 35503361870, 0] := by
  rw [show A10K2.u7361 = KTree.node A10K2.u7357 (nat_lit 120590952) (nat_lit 12014236270) (nat_lit 0) A10K2.u7360 from rfl, totK_node, atot7357, atot7360]
  decide +kernel

theorem arows7368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7368 = true := by
  rw [show A10K2.u7368 = KTree.node A10K2.u7364 (nat_lit 120637188) (nat_lit 13094388420) (nat_lit 0) A10K2.u7367 from rfl, allE_node, arows7364, irow7368, arows7367]
  all_goals rfl

theorem atot7368 : totK PA10K2 A10K2.u7368 = [0, 0, 1058101880176, 6735831704360, 14918373190495, 12760598116142, 3320792145277, 282577153265, 5546304973, 0] := by
  rw [show A10K2.u7368 = KTree.node A10K2.u7364 (nat_lit 120637188) (nat_lit 13094388420) (nat_lit 0) A10K2.u7367 from rfl, totK_node, atot7364, atot7367]
  decide +kernel

theorem arows7376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7376 = true := by
  rw [show A10K2.u7376 = KTree.node A10K2.u7372 (nat_lit 120734976) (nat_lit 13167295648) (nat_lit 0) A10K2.u7375 from rfl, allE_node, arows7372, irow7376, arows7375]
  all_goals rfl

theorem atot7376 : totK PA10K2 A10K2.u7376 = [0, 0, 1382768741360, 8089999237339, 15789532000914, 10812737409619, 1914493784197, 86128664638, 0, 0] := by
  rw [show A10K2.u7376 = KTree.node A10K2.u7372 (nat_lit 120734976) (nat_lit 13167295648) (nat_lit 0) A10K2.u7375 from rfl, totK_node, atot7372, atot7375]
  decide +kernel

theorem arows7383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7383 = true := by
  rw [show A10K2.u7383 = KTree.node A10K2.u7379 (nat_lit 121112918) (nat_lit 11933677) (nat_lit 0) A10K2.u7382 from rfl, allE_node, arows7379, irow7383, arows7382]
  all_goals rfl

theorem atot7383 : totK PA10K2 A10K2.u7383 = [0, 0, 1372130172110, 7406415245431, 14347241422881, 11254712075352, 3058518569582, 289042469111, 6354482628, 0] := by
  rw [show A10K2.u7383 = KTree.node A10K2.u7379 (nat_lit 121112918) (nat_lit 11933677) (nat_lit 0) A10K2.u7382 from rfl, totK_node, atot7379, atot7382]
  decide +kernel

theorem arows7392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7392 = true := by
  rw [show A10K2.u7392 = KTree.node A10K2.u7388 (nat_lit 121145507) (nat_lit 3728940620) (nat_lit 0) A10K2.u7391 from rfl, allE_node, arows7388, irow7392, arows7391]
  all_goals rfl

theorem atot7392 : totK PA10K2 A10K2.u7392 = [0, 0, 793449030898, 5681032547145, 13881301108101, 13739287212781, 4853512561698, 568084980045, 13364899180, 0] := by
  rw [show A10K2.u7392 = KTree.node A10K2.u7388 (nat_lit 121145507) (nat_lit 3728940620) (nat_lit 0) A10K2.u7391 from rfl, totK_node, atot7388, atot7391]
  decide +kernel

theorem arows7399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7399 = true := by
  rw [show A10K2.u7399 = KTree.node A10K2.u7395 (nat_lit 121201938) (nat_lit 15196763129) (nat_lit 0) A10K2.u7398 from rfl, allE_node, arows7395, irow7399, arows7398]
  all_goals rfl

theorem atot7399 : totK PA10K2 A10K2.u7399 = [0, 0, 1606735580082, 8604397034236, 15941231433828, 11763432348159, 2837918021440, 154037002291, 0, 0] := by
  rw [show A10K2.u7399 = KTree.node A10K2.u7395 (nat_lit 121201938) (nat_lit 15196763129) (nat_lit 0) A10K2.u7398 from rfl, totK_node, atot7395, atot7398]
  decide +kernel

theorem arows7407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7407 = true := by
  rw [show A10K2.u7407 = KTree.node A10K2.u7403 (nat_lit 121310869) (nat_lit 2960417477) (nat_lit 0) A10K2.u7406 from rfl, allE_node, arows7403, irow7407, arows7406]
  all_goals rfl

theorem atot7407 : totK PA10K2 A10K2.u7407 = [0, 0, 1631488299848, 8103921057389, 14826769726238, 11623370553245, 3566007696953, 338199386172, 7380853412, 0] := by
  rw [show A10K2.u7407 = KTree.node A10K2.u7403 (nat_lit 121310869) (nat_lit 2960417477) (nat_lit 0) A10K2.u7406 from rfl, totK_node, atot7403, atot7406]
  decide +kernel

theorem arows7414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7414 = true := by
  rw [show A10K2.u7414 = KTree.node A10K2.u7410 (nat_lit 121342014) (nat_lit 14819070181) (nat_lit 0) A10K2.u7413 from rfl, allE_node, arows7410, irow7414, arows7413]
  all_goals rfl

theorem atot7414 : totK PA10K2 A10K2.u7414 = [0, 0, 715278061713, 5143648415720, 13347656435453, 14321473603046, 5803835895040, 643188043533, 13671283666, 0] := by
  rw [show A10K2.u7414 = KTree.node A10K2.u7410 (nat_lit 121342014) (nat_lit 14819070181) (nat_lit 0) A10K2.u7413 from rfl, totK_node, atot7410, atot7413]
  decide +kernel

theorem arows7426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7426 = true := by
  rw [show A10K2.u7426 = KTree.node A10K2.u7422 (nat_lit 122234558) (nat_lit 15268314887) (nat_lit 0) A10K2.u7425 from rfl, allE_node, arows7422, irow7426, arows7425]
  all_goals rfl

theorem atot7426 : totK PA10K2 A10K2.u7426 = [0, 1555866292484, 6248272153942, 9272991624559, 8480034563659, 7656728269490, 4667462495073, 1029741685652, 61110126106, 0] := by
  rw [show A10K2.u7426 = KTree.node A10K2.u7422 (nat_lit 122234558) (nat_lit 15268314887) (nat_lit 0) A10K2.u7425 from rfl, totK_node, atot7422, atot7425]
  decide +kernel

theorem arows7433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7433 = true := by
  rw [show A10K2.u7433 = KTree.node A10K2.u7429 (nat_lit 122256859) (nat_lit 6511804193) (nat_lit 0) A10K2.u7432 from rfl, allE_node, arows7429, irow7433, arows7432]
  all_goals rfl

theorem atot7433 : totK PA10K2 A10K2.u7433 = [0, 788312884667, 5915694614741, 13910874584675, 12786358853411, 4728427855388, 678822986081, 31082886609, 0, 0] := by
  rw [show A10K2.u7433 = KTree.node A10K2.u7429 (nat_lit 122256859) (nat_lit 6511804193) (nat_lit 0) A10K2.u7432 from rfl, totK_node, atot7429, atot7432]
  decide +kernel

theorem arows7441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7441 = true := by
  rw [show A10K2.u7441 = KTree.node A10K2.u7437 (nat_lit 122296389) (nat_lit 6183231131) (nat_lit 0) A10K2.u7440 from rfl, allE_node, arows7437, irow7441, arows7440]
  all_goals rfl

theorem atot7441 : totK PA10K2 A10K2.u7441 = [0, 1449759372644, 7142261014653, 13670303124975, 11879707655468, 3864872862054, 366073782041, 6121173289, 0, 0] := by
  rw [show A10K2.u7441 = KTree.node A10K2.u7437 (nat_lit 122296389) (nat_lit 6183231131) (nat_lit 0) A10K2.u7440 from rfl, totK_node, atot7437, atot7440]
  decide +kernel

theorem arows7448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7448 = true := by
  rw [show A10K2.u7448 = KTree.node A10K2.u7444 (nat_lit 122339335) (nat_lit 9346727364) (nat_lit 0) A10K2.u7447 from rfl, allE_node, arows7444, irow7448, arows7447]
  all_goals rfl

theorem atot7448 : totK PA10K2 A10K2.u7448 = [0, 845446133736, 6383947565931, 14824017589300, 12712191099287, 3501126927281, 293059568946, 6354482628, 0, 0] := by
  rw [show A10K2.u7448 = KTree.node A10K2.u7444 (nat_lit 122339335) (nat_lit 9346727364) (nat_lit 0) A10K2.u7447 from rfl, totK_node, atot7444, atot7447]
  decide +kernel

theorem arows7457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7457 = true := by
  rw [show A10K2.u7457 = KTree.node A10K2.u7453 (nat_lit 122382165) (nat_lit 5992597342) (nat_lit 0) A10K2.u7456 from rfl, allE_node, arows7453, irow7457, arows7456]
  all_goals rfl

theorem atot7457 : totK PA10K2 A10K2.u7457 = [0, 1659408637769, 8306501501028, 15022526687524, 11556607131502, 3500633933719, 340195003851, 6904928264, 0, 0] := by
  rw [show A10K2.u7457 = KTree.node A10K2.u7453 (nat_lit 122382165) (nat_lit 5992597342) (nat_lit 0) A10K2.u7456 from rfl, totK_node, atot7453, atot7456]
  decide +kernel

theorem arows7464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7464 = true := by
  rw [show A10K2.u7464 = KTree.node A10K2.u7460 (nat_lit 122416291) (nat_lit 9951339791) (nat_lit 0) A10K2.u7463 from rfl, allE_node, arows7460, irow7464, arows7463]
  all_goals rfl

theorem atot7464 : totK PA10K2 A10K2.u7464 = [0, 0, 2528304371988, 11104586476987, 15973452237990, 8539029384122, 1474430238013, 68157151558, 0, 0] := by
  rw [show A10K2.u7464 = KTree.node A10K2.u7460 (nat_lit 122416291) (nat_lit 9951339791) (nat_lit 0) A10K2.u7463 from rfl, totK_node, atot7460, atot7463]
  decide +kernel

theorem arows7472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7472 = true := by
  rw [show A10K2.u7472 = KTree.node A10K2.u7468 (nat_lit 122511934) (nat_lit 15382517164) (nat_lit 0) A10K2.u7471 from rfl, allE_node, arows7468, irow7472, arows7471]
  all_goals rfl

theorem atot7472 : totK PA10K2 A10K2.u7472 = [0, 0, 1470347982880, 8274784611524, 15657606495256, 10780141919015, 2257327813605, 111594468326, 0, 0] := by
  rw [show A10K2.u7472 = KTree.node A10K2.u7468 (nat_lit 122511934) (nat_lit 15382517164) (nat_lit 0) A10K2.u7471 from rfl, totK_node, atot7468, atot7471]
  decide +kernel

theorem arows7479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7479 = true := by
  rw [show A10K2.u7479 = KTree.node A10K2.u7475 (nat_lit 122542624) (nat_lit 11758403416) (nat_lit 0) A10K2.u7478 from rfl, allE_node, arows7475, irow7479, arows7478]
  all_goals rfl

theorem atot7479 : totK PA10K2 A10K2.u7479 = [0, 0, 1050022894405, 5762490950154, 12376012342456, 12529738554875, 5369200250035, 843960814727, 36704093874, 0] := by
  rw [show A10K2.u7479 = KTree.node A10K2.u7475 (nat_lit 122542624) (nat_lit 11758403416) (nat_lit 0) A10K2.u7478 from rfl, totK_node, atot7475, atot7478]
  decide +kernel

theorem arows7489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7489 = true := by
  rw [show A10K2.u7489 = KTree.node A10K2.u7485 (nat_lit 122587296) (nat_lit 9074948959) (nat_lit 0) A10K2.u7488 from rfl, allE_node, arows7485, irow7489, arows7488]
  all_goals rfl

theorem atot7489 : totK PA10K2 A10K2.u7489 = [0, 0, 743454972142, 6015267701549, 14862157326533, 12894493911943, 3066487705255, 178739749965, 0, 0] := by
  rw [show A10K2.u7489 = KTree.node A10K2.u7485 (nat_lit 122587296) (nat_lit 9074948959) (nat_lit 0) A10K2.u7488 from rfl, totK_node, atot7485, atot7488]
  decide +kernel

theorem arows7496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7496 = true := by
  rw [show A10K2.u7496 = KTree.node A10K2.u7492 (nat_lit 122631838) (nat_lit 13652787407) (nat_lit 0) A10K2.u7495 from rfl, allE_node, arows7492, irow7496, arows7495]
  all_goals rfl

theorem atot7496 : totK PA10K2 A10K2.u7496 = [0, 0, 2166411084062, 10122171801758, 15993878310548, 9636280099046, 2066966039464, 182747950574, 6239673734, 0] := by
  rw [show A10K2.u7496 = KTree.node A10K2.u7492 (nat_lit 122631838) (nat_lit 13652787407) (nat_lit 0) A10K2.u7495 from rfl, totK_node, atot7492, atot7495]
  decide +kernel

theorem arows7504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7504 = true := by
  rw [show A10K2.u7504 = KTree.node A10K2.u7500 (nat_lit 122766622) (nat_lit 10947917954) (nat_lit 0) A10K2.u7503 from rfl, allE_node, arows7500, irow7504, arows7503]
  all_goals rfl

theorem atot7504 : totK PA10K2 A10K2.u7504 = [0, 2187980212392, 10120372552756, 15430004784096, 8648732446501, 2095716109838, 503389614575, 49137922124, 0, 0] := by
  rw [show A10K2.u7504 = KTree.node A10K2.u7500 (nat_lit 122766622) (nat_lit 10947917954) (nat_lit 0) A10K2.u7503 from rfl, totK_node, atot7500, atot7503]
  decide +kernel

theorem arows7511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7511 = true := by
  rw [show A10K2.u7511 = KTree.node A10K2.u7507 (nat_lit 122799461) (nat_lit 7280085236) (nat_lit 0) A10K2.u7510 from rfl, allE_node, arows7507, irow7511, arows7510]
  all_goals rfl

theorem atot7511 : totK PA10K2 A10K2.u7511 = [0, 561156172308, 4040852028175, 11676532122503, 14723441282029, 6700976978951, 933130336756, 37204059898, 0, 0] := by
  rw [show A10K2.u7511 = KTree.node A10K2.u7507 (nat_lit 122799461) (nat_lit 7280085236) (nat_lit 0) A10K2.u7510 from rfl, totK_node, atot7507, atot7510]
  decide +kernel

theorem arows7520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7520 = true := by
  rw [show A10K2.u7520 = KTree.node A10K2.u7516 (nat_lit 122830052) (nat_lit 11701526569) (nat_lit 0) A10K2.u7519 from rfl, allE_node, arows7516, irow7520, arows7519]
  all_goals rfl

theorem atot7520 : totK PA10K2 A10K2.u7520 = [0, 1587972465714, 8724602523505, 15718492161357, 10086657115884, 1937773399441, 100942782316, 0, 0, 0] := by
  rw [show A10K2.u7520 = KTree.node A10K2.u7516 (nat_lit 122830052) (nat_lit 11701526569) (nat_lit 0) A10K2.u7519 from rfl, totK_node, atot7516, atot7519]
  decide +kernel

theorem arows7527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7527 = true := by
  rw [show A10K2.u7527 = KTree.node A10K2.u7523 (nat_lit 122870304) (nat_lit 13047187047) (nat_lit 0) A10K2.u7526 from rfl, allE_node, arows7523, irow7527, arows7526]
  all_goals rfl

theorem atot7527 : totK PA10K2 A10K2.u7527 = [0, 0, 2857759403907, 11946240314789, 15584713190333, 6771362624239, 985521365426, 37807056478, 0, 0] := by
  rw [show A10K2.u7527 = KTree.node A10K2.u7523 (nat_lit 122870304) (nat_lit 13047187047) (nat_lit 0) A10K2.u7526 from rfl, totK_node, atot7523, atot7526]
  decide +kernel

theorem arows7535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7535 = true := by
  rw [show A10K2.u7535 = KTree.node A10K2.u7531 (nat_lit 123076890) (nat_lit 8793938566) (nat_lit 0) A10K2.u7534 from rfl, allE_node, arows7531, irow7535, arows7534]
  all_goals rfl

theorem atot7535 : totK PA10K2 A10K2.u7535 = [0, 0, 2211806556657, 10624912938310, 16423225458859, 8265970652783, 1151847657944, 43746946997, 0, 0] := by
  rw [show A10K2.u7535 = KTree.node A10K2.u7531 (nat_lit 123076890) (nat_lit 8793938566) (nat_lit 0) A10K2.u7534 from rfl, totK_node, atot7531, atot7534]
  decide +kernel

theorem arows7542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7542 = true := by
  rw [show A10K2.u7542 = KTree.node A10K2.u7538 (nat_lit 123111680) (nat_lit 14444943766) (nat_lit 0) A10K2.u7541 from rfl, allE_node, arows7538, irow7542, arows7541]
  all_goals rfl

theorem atot7542 : totK PA10K2 A10K2.u7542 = [0, 0, 819213633141, 6205572868046, 14860154289218, 12357792651444, 2912944252581, 168742233987, 0, 0] := by
  rw [show A10K2.u7542 = KTree.node A10K2.u7538 (nat_lit 123111680) (nat_lit 14444943766) (nat_lit 0) A10K2.u7541 from rfl, totK_node, atot7538, atot7541]
  decide +kernel

theorem arows7553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7553 = true := by
  rw [show A10K2.u7553 = KTree.node A10K2.u7549 (nat_lit 123235478) (nat_lit 15438790864) (nat_lit 0) A10K2.u7552 from rfl, allE_node, arows7549, irow7553, arows7552]
  all_goals rfl

theorem atot7553 : totK PA10K2 A10K2.u7553 = [0, 1602700457968, 8254466438886, 15171982300224, 11381737721981, 3134312582117, 614960066126, 136682872893, 6354482628, 0] := by
  rw [show A10K2.u7553 = KTree.node A10K2.u7549 (nat_lit 123235478) (nat_lit 15438790864) (nat_lit 0) A10K2.u7552 from rfl, totK_node, atot7549, atot7552]
  decide +kernel

theorem arows7560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7560 = true := by
  rw [show A10K2.u7560 = KTree.node A10K2.u7556 (nat_lit 123285381) (nat_lit 1254616384) (nat_lit 0) A10K2.u7559 from rfl, allE_node, arows7556, irow7560, arows7559]
  all_goals rfl

theorem atot7560 : totK PA10K2 A10K2.u7560 = [0, 1863642875799, 8640303797744, 14410286317921, 10495757212002, 3355618896246, 442479106924, 13364899180, 0, 0] := by
  rw [show A10K2.u7560 = KTree.node A10K2.u7556 (nat_lit 123285381) (nat_lit 1254616384) (nat_lit 0) A10K2.u7559 from rfl, totK_node, atot7556, atot7559]
  decide +kernel

theorem arows7568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7568 = true := by
  rw [show A10K2.u7568 = KTree.node A10K2.u7564 (nat_lit 123317755) (nat_lit 6239094582) (nat_lit 0) A10K2.u7567 from rfl, allE_node, arows7564, irow7568, arows7567]
  all_goals rfl

theorem atot7568 : totK PA10K2 A10K2.u7568 = [0, 319364795913, 4120286168743, 12768663097174, 14705795222365, 6235419837911, 896475963172, 37204059898, 0, 0] := by
  rw [show A10K2.u7568 = KTree.node A10K2.u7564 (nat_lit 123317755) (nat_lit 6239094582) (nat_lit 0) A10K2.u7567 from rfl, totK_node, atot7564, atot7567]
  decide +kernel

theorem arows7575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7575 = true := by
  rw [show A10K2.u7575 = KTree.node A10K2.u7571 (nat_lit 123414354) (nat_lit 14828695722) (nat_lit 0) A10K2.u7574 from rfl, allE_node, arows7571, irow7575, arows7574]
  all_goals rfl

theorem atot7575 : totK PA10K2 A10K2.u7575 = [0, 2347203525858, 10396107826222, 15759479182342, 9421645455339, 2048027770168, 126377474021, 0, 0, 0] := by
  rw [show A10K2.u7575 = KTree.node A10K2.u7571 (nat_lit 123414354) (nat_lit 14828695722) (nat_lit 0) A10K2.u7574 from rfl, totK_node, atot7571, atot7574]
  decide +kernel

theorem arows7584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7584 = true := by
  rw [show A10K2.u7584 = KTree.node A10K2.u7580 (nat_lit 123444443) (nat_lit 6004656855) (nat_lit 0) A10K2.u7583 from rfl, allE_node, arows7580, irow7584, arows7583]
  all_goals rfl

theorem atot7584 : totK PA10K2 A10K2.u7584 = [0, 0, 3172390593673, 12804123436170, 16300588837903, 6911976745054, 777619143032, 13951953716, 0, 0] := by
  rw [show A10K2.u7584 = KTree.node A10K2.u7580 (nat_lit 123444443) (nat_lit 6004656855) (nat_lit 0) A10K2.u7583 from rfl, totK_node, atot7580, atot7583]
  decide +kernel

theorem arows7591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7591 = true := by
  rw [show A10K2.u7591 = KTree.node A10K2.u7587 (nat_lit 123474310) (nat_lit 15557612177) (nat_lit 0) A10K2.u7590 from rfl, allE_node, arows7587, irow7591, arows7590]
  all_goals rfl

theorem atot7591 : totK PA10K2 A10K2.u7591 = [0, 0, 1766585276458, 9195745680047, 16246244142417, 10881467177814, 2173532073778, 93597249017, 0, 0] := by
  rw [show A10K2.u7591 = KTree.node A10K2.u7587 (nat_lit 123474310) (nat_lit 15557612177) (nat_lit 0) A10K2.u7590 from rfl, totK_node, atot7587, atot7590]
  decide +kernel

theorem arows7599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7599 = true := by
  rw [show A10K2.u7599 = KTree.node A10K2.u7595 (nat_lit 123530943) (nat_lit 14115639999) (nat_lit 0) A10K2.u7598 from rfl, allE_node, arows7595, irow7599, arows7598]
  all_goals rfl

theorem atot7599 : totK PA10K2 A10K2.u7599 = [0, 0, 1262604785756, 6814107004680, 14090775162547, 12745995442541, 4174955913035, 393572346808, 7007974415, 0] := by
  rw [show A10K2.u7599 = KTree.node A10K2.u7595 (nat_lit 123530943) (nat_lit 14115639999) (nat_lit 0) A10K2.u7598 from rfl, totK_node, atot7595, atot7598]
  decide +kernel

theorem arows7606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7606 = true := by
  rw [show A10K2.u7606 = KTree.node A10K2.u7602 (nat_lit 123567601) (nat_lit 8378157356) (nat_lit 0) A10K2.u7605 from rfl, allE_node, arows7602, irow7606, arows7605]
  all_goals rfl

theorem atot7606 : totK PA10K2 A10K2.u7606 = [0, 0, 920402885956, 6514576657920, 14665244475723, 12715621440920, 4060430151751, 410514728071, 7151180950, 0] := by
  rw [show A10K2.u7606 = KTree.node A10K2.u7602 (nat_lit 123567601) (nat_lit 8378157356) (nat_lit 0) A10K2.u7605 from rfl, totK_node, atot7602, atot7605]
  decide +kernel

theorem arows7616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7616 = true := by
  rw [show A10K2.u7616 = KTree.node A10K2.u7612 (nat_lit 123675936) (nat_lit 3811832379) (nat_lit 0) A10K2.u7615 from rfl, allE_node, arows7612, irow7616, arows7615]
  all_goals rfl

theorem atot7616 : totK PA10K2 A10K2.u7616 = [0, 0, 2314028796158, 10167234955724, 15689151116053, 9797922477411, 2020340686847, 93158680697, 0, 0] := by
  rw [show A10K2.u7616 = KTree.node A10K2.u7612 (nat_lit 123675936) (nat_lit 3811832379) (nat_lit 0) A10K2.u7615 from rfl, totK_node, atot7612, atot7615]
  decide +kernel

theorem arows7623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7623 = true := by
  rw [show A10K2.u7623 = KTree.node A10K2.u7619 (nat_lit 123705377) (nat_lit 9714518714) (nat_lit 0) A10K2.u7622 from rfl, allE_node, arows7619, irow7623, arows7622]
  all_goals rfl

theorem atot7623 : totK PA10K2 A10K2.u7623 = [0, 0, 17179869184, 3532131884848, 13297262553628, 16034218976032, 6308769975683, 658963546981, 12758098799, 0] := by
  rw [show A10K2.u7623 = KTree.node A10K2.u7619 (nat_lit 123705377) (nat_lit 9714518714) (nat_lit 0) A10K2.u7622 from rfl, totK_node, atot7619, atot7622]
  decide +kernel

theorem arows7631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7631 = true := by
  rw [show A10K2.u7631 = KTree.node A10K2.u7627 (nat_lit 124334065) (nat_lit 7561167579) (nat_lit 0) A10K2.u7630 from rfl, allE_node, arows7627, irow7631, arows7630]
  all_goals rfl

theorem atot7631 : totK PA10K2 A10K2.u7631 = [0, 0, 1733275277048, 7933244632248, 13141362078925, 10158752665625, 4636855003516, 999312560153, 61018386929, 0] := by
  rw [show A10K2.u7631 = KTree.node A10K2.u7627 (nat_lit 124334065) (nat_lit 7561167579) (nat_lit 0) A10K2.u7630 from rfl, totK_node, atot7627, atot7630]
  decide +kernel

theorem arows7638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7638 = true := by
  rw [show A10K2.u7638 = KTree.node A10K2.u7634 (nat_lit 124365669) (nat_lit 7169180454) (nat_lit 0) A10K2.u7637 from rfl, allE_node, arows7634, irow7638, arows7637]
  all_goals rfl

theorem atot7638 : totK PA10K2 A10K2.u7638 = [0, 0, 610900211470, 4691005045647, 12773091913533, 14152847243806, 5683442783495, 755846779956, 31082886609, 0] := by
  rw [show A10K2.u7638 = KTree.node A10K2.u7634 (nat_lit 124365669) (nat_lit 7169180454) (nat_lit 0) A10K2.u7637 from rfl, totK_node, atot7634, atot7637]
  decide +kernel

theorem arows7647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7647 = true := by
  rw [show A10K2.u7647 = KTree.node A10K2.u7643 (nat_lit 124400825) (nat_lit 3160980475) (nat_lit 0) A10K2.u7646 from rfl, allE_node, arows7643, irow7647, arows7646]
  all_goals rfl

theorem atot7647 : totK PA10K2 A10K2.u7647 = [0, 0, 1793477866547, 9101334711724, 15240531804377, 9814163517222, 2495486738541, 235909125327, 6121173289, 0] := by
  rw [show A10K2.u7647 = KTree.node A10K2.u7643 (nat_lit 124400825) (nat_lit 3160980475) (nat_lit 0) A10K2.u7646 from rfl, totK_node, atot7643, atot7646]
  decide +kernel

theorem arows7654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7654 = true := by
  rw [show A10K2.u7654 = KTree.node A10K2.u7650 (nat_lit 124443393) (nat_lit 9630807966) (nat_lit 0) A10K2.u7653 from rfl, allE_node, arows7650, irow7654, arows7653]
  all_goals rfl

theorem atot7654 : totK PA10K2 A10K2.u7654 = [0, 0, 1324242768764, 7218083555924, 14565151294224, 12318365558005, 3440582923832, 300792654152, 6354482628, 0] := by
  rw [show A10K2.u7654 = KTree.node A10K2.u7650 (nat_lit 124443393) (nat_lit 9630807966) (nat_lit 0) A10K2.u7653 from rfl, totK_node, atot7650, atot7653]
  decide +kernel

theorem arows7662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7662 = true := by
  rw [show A10K2.u7662 = KTree.node A10K2.u7658 (nat_lit 124485513) (nat_lit 7743170130) (nat_lit 0) A10K2.u7661 from rfl, allE_node, arows7658, irow7662, arows7661]
  all_goals rfl

theorem atot7662 : totK PA10K2 A10K2.u7662 = [0, 0, 846194190982, 5777398730180, 14142694592778, 13974060623398, 4967450109716, 491142614024, 7047025452, 0] := by
  rw [show A10K2.u7662 = KTree.node A10K2.u7658 (nat_lit 124485513) (nat_lit 7743170130) (nat_lit 0) A10K2.u7661 from rfl, totK_node, atot7658, atot7661]
  decide +kernel

theorem arows7669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7669 = true := by
  rw [show A10K2.u7669 = KTree.node A10K2.u7665 (nat_lit 124593960) (nat_lit 8350982014) (nat_lit 0) A10K2.u7668 from rfl, allE_node, arows7665, irow7669, arows7668]
  all_goals rfl

theorem atot7669 : totK PA10K2 A10K2.u7669 = [0, 0, 0, 2392552583244, 10642496484955, 15688083441151, 8606899376974, 1538737021841, 72899043879, 0] := by
  rw [show A10K2.u7669 = KTree.node A10K2.u7665 (nat_lit 124593960) (nat_lit 8350982014) (nat_lit 0) A10K2.u7668 from rfl, totK_node, atot7665, atot7668]
  decide +kernel

theorem arows7682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7682 = true := by
  rw [show A10K2.u7682 = KTree.node A10K2.u7678 (nat_lit 124626431) (nat_lit 13306701449) (nat_lit 0) A10K2.u7681 from rfl, allE_node, arows7678, irow7682, arows7681]
  all_goals rfl

theorem atot7682 : totK PA10K2 A10K2.u7682 = [0, 0, 0, 780536075463, 6174543412717, 14754806163169, 12705465789656, 3847523465093, 405839665934, 8047840951] := by
  rw [show A10K2.u7682 = KTree.node A10K2.u7678 (nat_lit 124626431) (nat_lit 13306701449) (nat_lit 0) A10K2.u7681 from rfl, totK_node, atot7678, atot7681]
  decide +kernel

theorem arows7689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7689 = true := by
  rw [show A10K2.u7689 = KTree.node A10K2.u7685 (nat_lit 124666377) (nat_lit 9326104932) (nat_lit 0) A10K2.u7688 from rfl, allE_node, arows7685, irow7689, arows7688]
  all_goals rfl

theorem atot7689 : totK PA10K2 A10K2.u7689 = [0, 0, 0, 2806172197914, 11822179966495, 15746979827991, 7174955581924, 1117316377604, 55712700593, 0] := by
  rw [show A10K2.u7689 = KTree.node A10K2.u7685 (nat_lit 124666377) (nat_lit 9326104932) (nat_lit 0) A10K2.u7688 from rfl, totK_node, atot7685, atot7688]
  decide +kernel

theorem arows7697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7697 = true := by
  rw [show A10K2.u7697 = KTree.node A10K2.u7693 (nat_lit 124745384) (nat_lit 2426756781) (nat_lit 0) A10K2.u7696 from rfl, allE_node, arows7693, irow7697, arows7696]
  all_goals rfl

theorem atot7697 : totK PA10K2 A10K2.u7697 = [0, 0, 948444040241, 5305485221679, 12097040525987, 13358692403718, 6654460799250, 1183041110267, 55162827605, 0] := by
  rw [show A10K2.u7697 = KTree.node A10K2.u7693 (nat_lit 124745384) (nat_lit 2426756781) (nat_lit 0) A10K2.u7696 from rfl, totK_node, atot7693, atot7696]
  decide +kernel

theorem arows7704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7704 = true := by
  rw [show A10K2.u7704 = KTree.node A10K2.u7700 (nat_lit 124876564) (nat_lit 11846929894) (nat_lit 0) A10K2.u7703 from rfl, allE_node, arows7700, irow7704, arows7703]
  all_goals rfl

theorem atot7704 : totK PA10K2 A10K2.u7704 = [0, 0, 2567840373125, 11179219597976, 16008436721347, 8013014096551, 1147154276330, 30041515203, 0, 0] := by
  rw [show A10K2.u7704 = KTree.node A10K2.u7700 (nat_lit 124876564) (nat_lit 11846929894) (nat_lit 0) A10K2.u7703 from rfl, totK_node, atot7700, atot7703]
  decide +kernel

theorem arows7713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7713 = true := by
  rw [show A10K2.u7713 = KTree.node A10K2.u7709 (nat_lit 124934418) (nat_lit 14212334152) (nat_lit 0) A10K2.u7712 from rfl, allE_node, arows7709, irow7713, arows7712]
  all_goals rfl

theorem atot7713 : totK PA10K2 A10K2.u7713 = [0, 0, 820824437048, 6885911163911, 15720093786534, 11972676566616, 2393791720348, 123873645124, 0, 0] := by
  rw [show A10K2.u7713 = KTree.node A10K2.u7709 (nat_lit 124934418) (nat_lit 14212334152) (nat_lit 0) A10K2.u7712 from rfl, totK_node, atot7709, atot7712]
  decide +kernel

theorem arows7720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7720 = true := by
  rw [show A10K2.u7720 = KTree.node A10K2.u7716 (nat_lit 125329526) (nat_lit 15894490354) (nat_lit 0) A10K2.u7719 from rfl, allE_node, arows7716, irow7720, arows7719]
  all_goals rfl

theorem atot7720 : totK PA10K2 A10K2.u7720 = [0, 0, 1602700457968, 8105788166903, 14868302121218, 11618874801050, 3414156696623, 319388456036, 6354482628, 0] := by
  rw [show A10K2.u7720 = KTree.node A10K2.u7716 (nat_lit 125329526) (nat_lit 15894490354) (nat_lit 0) A10K2.u7719 from rfl, totK_node, atot7716, atot7719]
  decide +kernel

theorem arows7728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7728 = true := by
  rw [show A10K2.u7728 = KTree.node A10K2.u7724 (nat_lit 125381302) (nat_lit 15076288878) (nat_lit 0) A10K2.u7727 from rfl, allE_node, arows7724, irow7728, arows7727]
  all_goals rfl

theorem atot7728 : totK PA10K2 A10K2.u7728 = [0, 0, 1523643848986, 7632870779419, 14450989496780, 11778626933155, 3632188898060, 343414877022, 7237400819, 0] := by
  rw [show A10K2.u7728 = KTree.node A10K2.u7724 (nat_lit 125381302) (nat_lit 15076288878) (nat_lit 0) A10K2.u7727 from rfl, totK_node, atot7724, atot7727]
  decide +kernel

theorem arows7735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7735 = true := by
  rw [show A10K2.u7735 = KTree.node A10K2.u7731 (nat_lit 125413738) (nat_lit 9865715108) (nat_lit 0) A10K2.u7734 from rfl, allE_node, arows7731, irow7735, arows7734]
  all_goals rfl

theorem atot7735 : totK PA10K2 A10K2.u7735 = [0, 0, 659363822726, 5130314378646, 13366884198540, 14259109212713, 5527576548636, 632317063263, 13576218110, 0] := by
  rw [show A10K2.u7735 = KTree.node A10K2.u7731 (nat_lit 125413738) (nat_lit 9865715108) (nat_lit 0) A10K2.u7734 from rfl, totK_node, atot7731, atot7734]
  decide +kernel

theorem arows7745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7745 = true := by
  rw [show A10K2.u7745 = KTree.node A10K2.u7741 (nat_lit 125511354) (nat_lit 14950583633) (nat_lit 0) A10K2.u7744 from rfl, allE_node, arows7741, irow7745, arows7744]
  all_goals rfl

theorem atot7745 : totK PA10K2 A10K2.u7745 = [0, 0, 2347203525858, 10396449621895, 15844631228886, 9382432526655, 1974913236012, 100426065937, 0, 0] := by
  rw [show A10K2.u7745 = KTree.node A10K2.u7741 (nat_lit 125511354) (nat_lit 14950583633) (nat_lit 0) A10K2.u7744 from rfl, totK_node, atot7741, atot7744]
  decide +kernel

theorem arows7752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7752 = true := by
  rw [show A10K2.u7752 = KTree.node A10K2.u7748 (nat_lit 125541561) (nat_lit 5815995929) (nat_lit 0) A10K2.u7751 from rfl, allE_node, arows7748, irow7752, arows7751]
  all_goals rfl

theorem atot7752 : totK PA10K2 A10K2.u7752 = [0, 0, 0, 3311235370909, 13058250313532, 16193778844893, 6611871659879, 703718699482, 13679205470, 0] := by
  rw [show A10K2.u7752 = KTree.node A10K2.u7748 (nat_lit 125541561) (nat_lit 5815995929) (nat_lit 0) A10K2.u7751 from rfl, totK_node, atot7748, atot7751]
  decide +kernel

theorem arows7760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7760 = true := by
  rw [show A10K2.u7760 = KTree.node A10K2.u7756 (nat_lit 130027553) (nat_lit 10204605750) (nat_lit 0) A10K2.u7759 from rfl, allE_node, arows7756, irow7760, arows7759]
  all_goals rfl

theorem atot7760 : totK PA10K2 A10K2.u7760 = [0, 1766182138642, 7774614574895, 11426683826199, 7427619251400, 5272004266631, 3824259744207, 967713448238, 61110126106, 0] := by
  rw [show A10K2.u7760 = KTree.node A10K2.u7756 (nat_lit 130027553) (nat_lit 10204605750) (nat_lit 0) A10K2.u7759 from rfl, totK_node, atot7756, atot7759]
  decide +kernel

theorem arows7767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7767 = true := by
  rw [show A10K2.u7767 = KTree.node A10K2.u7763 (nat_lit 130059766) (nat_lit 16824835909) (nat_lit 0) A10K2.u7766 from rfl, allE_node, arows7763, irow7767, arows7766]
  all_goals rfl

theorem atot7767 : totK PA10K2 A10K2.u7767 = [0, 465644095695, 4315790162660, 12607945327561, 14443881594879, 5981183114704, 876770374062, 36196801203, 0, 0] := by
  rw [show A10K2.u7767 = KTree.node A10K2.u7763 (nat_lit 130059766) (nat_lit 16824835909) (nat_lit 0) A10K2.u7766 from rfl, totK_node, atot7763, atot7766]
  decide +kernel

theorem arows7776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7776 = true := by
  rw [show A10K2.u7776 = KTree.node A10K2.u7772 (nat_lit 130170943) (nat_lit 11732207025) (nat_lit 0) A10K2.u7775 from rfl, allE_node, arows7772, irow7776, arows7775]
  all_goals rfl

theorem atot7776 : totK PA10K2 A10K2.u7776 = [0, 1318949507170, 7829294246329, 15493565587144, 11557567874320, 2709147924058, 158186759238, 0, 0, 0] := by
  rw [show A10K2.u7776 = KTree.node A10K2.u7772 (nat_lit 130170943) (nat_lit 11732207025) (nat_lit 0) A10K2.u7775 from rfl, totK_node, atot7772, atot7775]
  decide +kernel

theorem arows7783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7783 = true := by
  rw [show A10K2.u7783 = KTree.node A10K2.u7779 (nat_lit 130231510) (nat_lit 15177660555) (nat_lit 0) A10K2.u7782 from rfl, allE_node, arows7779, irow7783, arows7782]
  all_goals rfl

theorem atot7783 : totK PA10K2 A10K2.u7783 = [0, 2252464922703, 10299124826416, 16132710902183, 9412134033464, 1644440796351, 62616411126, 0, 0, 0] := by
  rw [show A10K2.u7783 = KTree.node A10K2.u7779 (nat_lit 130231510) (nat_lit 15177660555) (nat_lit 0) A10K2.u7782 from rfl, totK_node, atot7779, atot7782]
  decide +kernel

theorem arows7791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7791 = true := by
  rw [show A10K2.u7791 = KTree.node A10K2.u7787 (nat_lit 130262806) (nat_lit 11475567458) (nat_lit 0) A10K2.u7790 from rfl, allE_node, arows7787, irow7791, arows7790]
  all_goals rfl

theorem atot7791 : totK PA10K2 A10K2.u7791 = [0, 0, 2576972182881, 11417883696688, 16504360711935, 8198365277922, 1031793282425, 20018912194, 0, 0] := by
  rw [show A10K2.u7791 = KTree.node A10K2.u7787 (nat_lit 130262806) (nat_lit 11475567458) (nat_lit 0) A10K2.u7790 from rfl, totK_node, atot7787, atot7790]
  decide +kernel

theorem arows7798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7798 = true := by
  rw [show A10K2.u7798 = KTree.node A10K2.u7794 (nat_lit 130292915) (nat_lit 7501701244) (nat_lit 0) A10K2.u7797 from rfl, allE_node, arows7794, irow7798, arows7797]
  all_goals rfl

theorem atot7798 : totK PA10K2 A10K2.u7798 = [0, 0, 2231826234337, 10273646750530, 15695873411417, 8706898875490, 1664662293207, 91579861429, 0, 0] := by
  rw [show A10K2.u7798 = KTree.node A10K2.u7794 (nat_lit 130292915) (nat_lit 7501701244) (nat_lit 0) A10K2.u7797 from rfl, totK_node, atot7794, atot7797]
  decide +kernel

theorem arows7809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7809 = true := by
  rw [show A10K2.u7809 = KTree.node A10K2.u7805 (nat_lit 130326002) (nat_lit 10269808568) (nat_lit 0) A10K2.u7808 from rfl, allE_node, arows7805, irow7809, arows7808]
  all_goals rfl

theorem atot7809 : totK PA10K2 A10K2.u7809 = [0, 0, 539669932579, 4664046685279, 13078295531114, 14344655391466, 5306471845927, 623017936184, 13364899180, 0] := by
  rw [show A10K2.u7809 = KTree.node A10K2.u7805 (nat_lit 130326002) (nat_lit 10269808568) (nat_lit 0) A10K2.u7808 from rfl, totK_node, atot7805, atot7808]
  decide +kernel

theorem arows7816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7816 = true := by
  rw [show A10K2.u7816 = KTree.node A10K2.u7812 (nat_lit 130449857) (nat_lit 10313665080) (nat_lit 0) A10K2.u7815 from rfl, allE_node, arows7812, irow7816, arows7815]
  all_goals rfl

theorem atot7816 : totK PA10K2 A10K2.u7816 = [0, 0, 1571509483081, 8585484186443, 15829910518734, 10461469337741, 2049175136903, 92826566318, 0, 0] := by
  rw [show A10K2.u7816 = KTree.node A10K2.u7812 (nat_lit 130449857) (nat_lit 10313665080) (nat_lit 0) A10K2.u7815 from rfl, totK_node, atot7812, atot7815]
  decide +kernel

theorem arows7824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7824 = true := by
  rw [show A10K2.u7824 = KTree.node A10K2.u7820 (nat_lit 130508571) (nat_lit 9838264813) (nat_lit 0) A10K2.u7823 from rfl, allE_node, arows7820, irow7824, arows7823]
  all_goals rfl

theorem atot7824 : totK PA10K2 A10K2.u7824 = [0, 849876618421, 4388443662456, 10305312092914, 13840091315641, 8615049816691, 1763249828975, 87977137236, 0, 0] := by
  rw [show A10K2.u7824 = KTree.node A10K2.u7820 (nat_lit 130508571) (nat_lit 9838264813) (nat_lit 0) A10K2.u7823 from rfl, totK_node, atot7820, atot7823]
  decide +kernel

theorem arows7831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7831 = true := by
  rw [show A10K2.u7831 = KTree.node A10K2.u7827 (nat_lit 130638777) (nat_lit 6942798429) (nat_lit 0) A10K2.u7830 from rfl, allE_node, arows7827, irow7831, arows7830]
  all_goals rfl

theorem atot7831 : totK PA10K2 A10K2.u7831 = [0, 1388287699512, 8128415206731, 15750449304964, 11177084636340, 2472517820656, 133558060715, 0, 0, 0] := by
  rw [show A10K2.u7831 = KTree.node A10K2.u7827 (nat_lit 130638777) (nat_lit 6942798429) (nat_lit 0) A10K2.u7830 from rfl, totK_node, atot7827, atot7830]
  decide +kernel

theorem arows7840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7840 = true := by
  rw [show A10K2.u7840 = KTree.node A10K2.u7836 (nat_lit 130670982) (nat_lit 15746881228) (nat_lit 0) A10K2.u7839 from rfl, allE_node, arows7836, irow7840, arows7839]
  all_goals rfl

theorem atot7840 : totK PA10K2 A10K2.u7840 = [0, 762716802215, 4948924648441, 12361116058421, 13738197858502, 6113508778421, 909501664105, 37204059898, 0, 0] := by
  rw [show A10K2.u7840 = KTree.node A10K2.u7836 (nat_lit 130670982) (nat_lit 15746881228) (nat_lit 0) A10K2.u7839 from rfl, totK_node, atot7836, atot7839]
  decide +kernel

theorem arows7847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7847 = true := by
  rw [show A10K2.u7847 = KTree.node A10K2.u7843 (nat_lit 130729371) (nat_lit 9832932674) (nat_lit 0) A10K2.u7846 from rfl, allE_node, arows7843, irow7847, arows7846]
  all_goals rfl

theorem atot7847 : totK PA10K2 A10K2.u7847 = [0, 1760149773565, 8928395010083, 15737751113407, 10618135410992, 2148143336879, 101964804356, 0, 0, 0] := by
  rw [show A10K2.u7847 = KTree.node A10K2.u7843 (nat_lit 130729371) (nat_lit 9832932674) (nat_lit 0) A10K2.u7846 from rfl, totK_node, atot7843, atot7846]
  decide +kernel

theorem arows7855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7855 = true := by
  rw [show A10K2.u7855 = KTree.node A10K2.u7851 (nat_lit 130773569) (nat_lit 10241432930) (nat_lit 0) A10K2.u7854 from rfl, allE_node, arows7851, irow7855, arows7854]
  all_goals rfl

theorem atot7855 : totK PA10K2 A10K2.u7855 = [0, 1054693577800, 6621440171410, 14467118535024, 12993522114029, 4426167709346, 445678146543, 6904928264, 0, 0] := by
  rw [show A10K2.u7855 = KTree.node A10K2.u7851 (nat_lit 130773569) (nat_lit 10241432930) (nat_lit 0) A10K2.u7854 from rfl, totK_node, atot7851, atot7854]
  decide +kernel

theorem arows7862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7862 = true := by
  rw [show A10K2.u7862 = KTree.node A10K2.u7858 (nat_lit 130806163) (nat_lit 8635382435) (nat_lit 0) A10K2.u7861 from rfl, allE_node, arows7858, irow7862, arows7861]
  all_goals rfl

theorem atot7862 : totK PA10K2 A10K2.u7862 = [0, 0, 2204918330441, 10191649365755, 15820756195547, 9319477155582, 1782133934763, 93891684850, 0, 0] := by
  rw [show A10K2.u7862 = KTree.node A10K2.u7858 (nat_lit 130806163) (nat_lit 8635382435) (nat_lit 0) A10K2.u7861 from rfl, totK_node, atot7858, atot7861]
  decide +kernel

theorem arows7872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7872 = true := by
  rw [show A10K2.u7872 = KTree.node A10K2.u7868 (nat_lit 130903709) (nat_lit 5220556409) (nat_lit 0) A10K2.u7871 from rfl, allE_node, arows7868, irow7872, arows7871]
  all_goals rfl

theorem atot7872 : totK PA10K2 A10K2.u7872 = [0, 0, 1386819479308, 7686768189600, 14819470829927, 11306896169217, 3307612588410, 409477116120, 13576218110, 0] := by
  rw [show A10K2.u7872 = KTree.node A10K2.u7868 (nat_lit 130903709) (nat_lit 5220556409) (nat_lit 0) A10K2.u7871 from rfl, totK_node, atot7868, atot7871]
  decide +kernel

theorem arows7879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7879 = true := by
  rw [show A10K2.u7879 = KTree.node A10K2.u7875 (nat_lit 130950820) (nat_lit 13034769765) (nat_lit 0) A10K2.u7878 from rfl, allE_node, arows7875, irow7879, arows7878]
  all_goals rfl

theorem atot7879 : totK PA10K2 A10K2.u7879 = [0, 0, 1323467222442, 7419395858615, 14602141323309, 11804475753202, 3539692973027, 282237987286, 0, 0] := by
  rw [show A10K2.u7879 = KTree.node A10K2.u7875 (nat_lit 130950820) (nat_lit 13034769765) (nat_lit 0) A10K2.u7878 from rfl, totK_node, atot7875, atot7878]
  decide +kernel

theorem arows7887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7887 = true := by
  rw [show A10K2.u7887 = KTree.node A10K2.u7883 (nat_lit 131010546) (nat_lit 13386070714) (nat_lit 0) A10K2.u7886 from rfl, allE_node, arows7883, irow7887, arows7886]
  all_goals rfl

theorem atot7887 : totK PA10K2 A10K2.u7887 = [0, 0, 1637531495016, 8522367261131, 15828819906480, 11191723383037, 2186245836478, 83562720984, 0, 0] := by
  rw [show A10K2.u7887 = KTree.node A10K2.u7883 (nat_lit 131010546) (nat_lit 13386070714) (nat_lit 0) A10K2.u7886 from rfl, totK_node, atot7883, atot7886]
  decide +kernel

theorem arows7894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7894 = true := by
  rw [show A10K2.u7894 = KTree.node A10K2.u7890 (nat_lit 131598612) (nat_lit 8130677970) (nat_lit 0) A10K2.u7893 from rfl, allE_node, arows7890, irow7894, arows7893]
  all_goals rfl

theorem atot7894 : totK PA10K2 A10K2.u7894 = [0, 1540001081091, 7218893546069, 12727779997268, 11099966402525, 5269526092049, 1085908752267, 62382159641, 0, 0] := by
  rw [show A10K2.u7894 = KTree.node A10K2.u7890 (nat_lit 131598612) (nat_lit 8130677970) (nat_lit 0) A10K2.u7893 from rfl, totK_node, atot7890, atot7893]
  decide +kernel

theorem arows7903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7903 = true := by
  rw [show A10K2.u7903 = KTree.node A10K2.u7899 (nat_lit 131631972) (nat_lit 13582197741) (nat_lit 0) A10K2.u7902 from rfl, allE_node, arows7899, irow7903, arows7902]
  all_goals rfl

theorem atot7903 : totK PA10K2 A10K2.u7903 = [0, 540969523310, 4766811243605, 13161575023853, 14235087533673, 5640258340514, 729042602517, 18459763130, 0, 0] := by
  rw [show A10K2.u7903 = KTree.node A10K2.u7899 (nat_lit 131631972) (nat_lit 13582197741) (nat_lit 0) A10K2.u7902 from rfl, totK_node, atot7899, atot7902]
  decide +kernel

theorem arows7910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7910 = true := by
  rw [show A10K2.u7910 = KTree.node A10K2.u7906 (nat_lit 131679389) (nat_lit 6181965923) (nat_lit 0) A10K2.u7909 from rfl, allE_node, arows7906, irow7910, arows7909]
  all_goals rfl

theorem atot7910 : totK PA10K2 A10K2.u7910 = [0, 2088351472436, 9790902353668, 15781657162054, 9842005620259, 2050055291838, 103134365698, 0, 0, 0] := by
  rw [show A10K2.u7910 = KTree.node A10K2.u7906 (nat_lit 131679389) (nat_lit 6181965923) (nat_lit 0) A10K2.u7909 from rfl, totK_node, atot7906, atot7909]
  decide +kernel

theorem arows7918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7918 = true := by
  rw [show A10K2.u7918 = KTree.node A10K2.u7914 (nat_lit 131712662) (nat_lit 14090307283) (nat_lit 0) A10K2.u7917 from rfl, allE_node, arows7914, irow7918, arows7917]
  all_goals rfl

theorem atot7918 : totK PA10K2 A10K2.u7918 = [0, 762038499923, 4812657596722, 12263785185828, 14192122963328, 6208828245936, 800141023906, 18713227901, 0, 0] := by
  rw [show A10K2.u7918 = KTree.node A10K2.u7914 (nat_lit 131712662) (nat_lit 14090307283) (nat_lit 0) A10K2.u7917 from rfl, totK_node, atot7914, atot7917]
  decide +kernel

theorem arows7925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7925 = true := by
  rw [show A10K2.u7925 = KTree.node A10K2.u7921 (nat_lit 131807917) (nat_lit 5669965449) (nat_lit 0) A10K2.u7924 from rfl, allE_node, arows7921, irow7925, arows7924]
  all_goals rfl

theorem atot7925 : totK PA10K2 A10K2.u7925 = [0, 1662197905889, 8942394844406, 16051486059207, 10695801599832, 2245876650426, 110242674966, 0, 0, 0] := by
  rw [show A10K2.u7925 = KTree.node A10K2.u7921 (nat_lit 131807917) (nat_lit 5669965449) (nat_lit 0) A10K2.u7924 from rfl, totK_node, atot7921, atot7924]
  decide +kernel

theorem arows7937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7937 = true := by
  rw [show A10K2.u7937 = KTree.node A10K2.u7933 (nat_lit 131837652) (nat_lit 9274611514) (nat_lit 0) A10K2.u7936 from rfl, allE_node, arows7933, irow7937, arows7936]
  all_goals rfl

theorem atot7937 : totK PA10K2 A10K2.u7937 = [0, 0, 2393165897516, 10989441260945, 16361154963593, 8520317685003, 1166237814121, 26176060751, 0, 0] := by
  rw [show A10K2.u7937 = KTree.node A10K2.u7933 (nat_lit 131837652) (nat_lit 9274611514) (nat_lit 0) A10K2.u7936 from rfl, totK_node, atot7933, atot7936]
  decide +kernel

theorem arows7944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7944 = true := by
  rw [show A10K2.u7944 = KTree.node A10K2.u7940 (nat_lit 131875368) (nat_lit 12594929656) (nat_lit 0) A10K2.u7943 from rfl, allE_node, arows7940, irow7944, arows7943]
  all_goals rfl

theorem atot7944 : totK PA10K2 A10K2.u7944 = [0, 0, 2078967978190, 9942505302669, 15953461777411, 9412499998446, 1766159439751, 80585324738, 0, 0] := by
  rw [show A10K2.u7944 = KTree.node A10K2.u7940 (nat_lit 131875368) (nat_lit 12594929656) (nat_lit 0) A10K2.u7943 from rfl, totK_node, atot7940, atot7943]
  decide +kernel

theorem arows7952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7952 = true := by
  rw [show A10K2.u7952 = KTree.node A10K2.u7948 (nat_lit 131916179) (nat_lit 8198192569) (nat_lit 0) A10K2.u7951 from rfl, allE_node, arows7948, irow7952, arows7951]
  all_goals rfl

theorem atot7952 : totK PA10K2 A10K2.u7952 = [0, 0, 810541816207, 5558449961310, 13785818341323, 13745438777854, 4571226648905, 421786281187, 7007974415, 0] := by
  rw [show A10K2.u7952 = KTree.node A10K2.u7948 (nat_lit 131916179) (nat_lit 8198192569) (nat_lit 0) A10K2.u7951 from rfl, totK_node, atot7948, atot7951]
  decide +kernel

theorem arows7959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7959 = true := by
  rw [show A10K2.u7959 = KTree.node A10K2.u7955 (nat_lit 131953875) (nat_lit 10853699543) (nat_lit 0) A10K2.u7958 from rfl, allE_node, arows7955, irow7959, arows7958]
  all_goals rfl

theorem atot7959 : totK PA10K2 A10K2.u7959 = [0, 0, 1275812037487, 7287956598512, 14630663784650, 12192342642224, 3786109562845, 355533152988, 7151180950, 0] := by
  rw [show A10K2.u7959 = KTree.node A10K2.u7955 (nat_lit 131953875) (nat_lit 10853699543) (nat_lit 0) A10K2.u7958 from rfl, totK_node, atot7955, atot7958]
  decide +kernel

theorem arows7968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7968 = true := by
  rw [show A10K2.u7968 = KTree.node A10K2.u7964 (nat_lit 132059905) (nat_lit 10313294501) (nat_lit 0) A10K2.u7967 from rfl, allE_node, arows7964, irow7968, arows7967]
  all_goals rfl

theorem atot7968 : totK PA10K2 A10K2.u7968 = [0, 0, 1807514382083, 9167520756809, 15865035138316, 10472369485936, 2114352343104, 93158680697, 0, 0] := by
  rw [show A10K2.u7968 = KTree.node A10K2.u7964 (nat_lit 132059905) (nat_lit 10313294501) (nat_lit 0) A10K2.u7967 from rfl, totK_node, atot7964, atot7967]
  decide +kernel

theorem arows7975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7975 = true := by
  rw [show A10K2.u7975 = KTree.node A10K2.u7971 (nat_lit 132091067) (nat_lit 6902461808) (nat_lit 0) A10K2.u7974 from rfl, allE_node, arows7971, irow7975, arows7974]
  all_goals rfl

theorem atot7975 : totK PA10K2 A10K2.u7975 = [0, 0, 613737279027, 4790686000814, 13110930973185, 14626260509847, 5835388938105, 636854903484, 12758098799, 0] := by
  rw [show A10K2.u7975 = KTree.node A10K2.u7971 (nat_lit 132091067) (nat_lit 6902461808) (nat_lit 0) A10K2.u7974 from rfl, totK_node, atot7971, atot7974]
  decide +kernel

theorem arows7983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7983 = true := by
  rw [show A10K2.u7983 = KTree.node A10K2.u7979 (nat_lit 132122661) (nat_lit 7254958379) (nat_lit 0) A10K2.u7982 from rfl, allE_node, arows7979, irow7983, arows7982]
  all_goals rfl

theorem atot7983 : totK PA10K2 A10K2.u7983 = [0, 0, 1429448720302, 7190786250352, 13058695367980, 10983052220004, 4996785857105, 1014129646055, 61018386929, 0] := by
  rw [show A10K2.u7983 = KTree.node A10K2.u7979 (nat_lit 132122661) (nat_lit 7254958379) (nat_lit 0) A10K2.u7982 from rfl, totK_node, atot7979, atot7982]
  decide +kernel

theorem arows7990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7990 = true := by
  rw [show A10K2.u7990 = KTree.node A10K2.u7986 (nat_lit 132153970) (nat_lit 7223317417) (nat_lit 0) A10K2.u7989 from rfl, allE_node, arows7986, irow7990, arows7989]
  all_goals rfl

theorem atot7990 : totK PA10K2 A10K2.u7990 = [0, 0, 802361088133, 5305308873378, 13199362399776, 13756353525764, 5179951961663, 606007310691, 13364899180, 0] := by
  rw [show A10K2.u7990 = KTree.node A10K2.u7986 (nat_lit 132153970) (nat_lit 7223317417) (nat_lit 0) A10K2.u7989 from rfl, totK_node, atot7986, atot7989]
  decide +kernel

theorem arows8000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8000 = true := by
  rw [show A10K2.u8000 = KTree.node A10K2.u7996 (nat_lit 132258061) (nat_lit 5928795439) (nat_lit 0) A10K2.u7999 from rfl, allE_node, arows7996, irow8000, arows7999]
  all_goals rfl

theorem atot8000 : totK PA10K2 A10K2.u8000 = [0, 0, 1316088719689, 7660011891330, 15391005453442, 11760400873066, 2772936628305, 156730799280, 0, 0] := by
  rw [show A10K2.u8000 = KTree.node A10K2.u7996 (nat_lit 132258061) (nat_lit 5928795439) (nat_lit 0) A10K2.u7999 from rfl, totK_node, atot7996, atot7999]
  decide +kernel

theorem arows8007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8007 = true := by
  rw [show A10K2.u8007 = KTree.node A10K2.u8003 (nat_lit 132329371) (nat_lit 8567532811) (nat_lit 0) A10K2.u8006 from rfl, allE_node, arows8003, irow8007, arows8006]
  all_goals rfl

theorem atot8007 : totK PA10K2 A10K2.u8007 = [0, 0, 2252461234070, 10448057955733, 16202801978230, 9240065966726, 1617370225951, 51311281750, 0, 0] := by
  rw [show A10K2.u8007 = KTree.node A10K2.u8003 (nat_lit 132329371) (nat_lit 8567532811) (nat_lit 0) A10K2.u8006 from rfl, totK_node, atot8003, atot8006]
  decide +kernel

theorem arows8015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8015 = true := by
  rw [show A10K2.u8015 = KTree.node A10K2.u8011 (nat_lit 132361787) (nat_lit 5862211277) (nat_lit 0) A10K2.u8014 from rfl, allE_node, arows8011, irow8015, arows8014]
  all_goals rfl

theorem atot8015 : totK PA10K2 A10K2.u8015 = [0, 0, 0, 2296316697255, 10891093002255, 16639927919453, 8673249560713, 1146682393548, 25895390701, 0] := by
  rw [show A10K2.u8015 = KTree.node A10K2.u8011 (nat_lit 132361787) (nat_lit 5862211277) (nat_lit 0) A10K2.u8014 from rfl, totK_node, atot8011, atot8014]
  decide +kernel

theorem arows8022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8022 = true := by
  rw [show A10K2.u8022 = KTree.node A10K2.u8018 (nat_lit 132399884) (nat_lit 11917901536) (nat_lit 0) A10K2.u8021 from rfl, allE_node, arows8018, irow8022, arows8021]
  all_goals rfl

theorem atot8022 : totK PA10K2 A10K2.u8022 = [0, 0, 0, 2231809808435, 10414867040007, 15981264808278, 8835385388385, 1528785242063, 69104266259, 0] := by
  rw [show A10K2.u8022 = KTree.node A10K2.u8018 (nat_lit 132399884) (nat_lit 11917901536) (nat_lit 0) A10K2.u8021 from rfl, totK_node, atot8018, atot8021]
  decide +kernel

theorem arows8031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8031 = true := by
  rw [show A10K2.u8031 = KTree.node A10K2.u8027 (nat_lit 132441279) (nat_lit 10972646350) (nat_lit 0) A10K2.u8030 from rfl, allE_node, arows8027, irow8031, arows8030]
  all_goals rfl

theorem atot8031 : totK PA10K2 A10K2.u8031 = [0, 0, 0, 1430762851388, 7945602205092, 14757907029116, 11120057970731, 3256965823609, 324687125292, 7237400819] := by
  rw [show A10K2.u8031 = KTree.node A10K2.u8027 (nat_lit 132441279) (nat_lit 10972646350) (nat_lit 0) A10K2.u8030 from rfl, totK_node, atot8027, atot8030]
  decide +kernel

theorem arows8038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8038 = true := by
  rw [show A10K2.u8038 = KTree.node A10K2.u8034 (nat_lit 132593051) (nat_lit 9859220283) (nat_lit 0) A10K2.u8037 from rfl, allE_node, arows8034, irow8038, arows8037]
  all_goals rfl

theorem atot8038 : totK PA10K2 A10K2.u8038 = [0, 0, 0, 2136634787484, 10229642328186, 16254852911328, 9445069733675, 1609727119007, 50013492352, 0] := by
  rw [show A10K2.u8038 = KTree.node A10K2.u8034 (nat_lit 132593051) (nat_lit 9859220283) (nat_lit 0) A10K2.u8037 from rfl, totK_node, atot8034, atot8037]
  decide +kernel

theorem arows8046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8046 = true := by
  rw [show A10K2.u8046 = KTree.node A10K2.u8042 (nat_lit 132729078) (nat_lit 11784030277) (nat_lit 0) A10K2.u8045 from rfl, allE_node, arows8042, irow8046, arows8045]
  all_goals rfl

theorem atot8046 : totK PA10K2 A10K2.u8046 = [0, 0, 2238147892032, 10366089132776, 15960529458121, 8910890222227, 1594456773924, 172871998135, 31688522620, 0] := by
  rw [show A10K2.u8046 = KTree.node A10K2.u8042 (nat_lit 132729078) (nat_lit 11784030277) (nat_lit 0) A10K2.u8045 from rfl, totK_node, atot8042, atot8045]
  decide +kernel

theorem arows8053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8053 = true := by
  rw [show A10K2.u8053 = KTree.node A10K2.u8049 (nat_lit 132761874) (nat_lit 14319394923) (nat_lit 0) A10K2.u8052 from rfl, allE_node, arows8049, irow8053, arows8052]
  all_goals rfl

theorem atot8053 : totK PA10K2 A10K2.u8053 = [0, 0, 762716802215, 5029695550956, 12732077506352, 14119001315582, 5830237413879, 682594994666, 13576218110, 0] := by
  rw [show A10K2.u8053 = KTree.node A10K2.u8049 (nat_lit 132761874) (nat_lit 14319394923) (nat_lit 0) A10K2.u8052 from rfl, totK_node, atot8049, atot8052]
  decide +kernel

theorem arows8064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8064 = true := by
  rw [show A10K2.u8064 = KTree.node A10K2.u8060 (nat_lit 132826468) (nat_lit 13782022761) (nat_lit 0) A10K2.u8063 from rfl, allE_node, arows8060, irow8064, arows8063]
  all_goals rfl

theorem atot8064 : totK PA10K2 A10K2.u8064 = [0, 0, 1943326293240, 9532284143244, 15896330682462, 9983362431456, 1997940389646, 89706456049, 0, 0] := by
  rw [show A10K2.u8064 = KTree.node A10K2.u8060 (nat_lit 132826468) (nat_lit 13782022761) (nat_lit 0) A10K2.u8063 from rfl, totK_node, atot8060, atot8063]
  decide +kernel

theorem arows8071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8071 = true := by
  rw [show A10K2.u8071 = KTree.node A10K2.u8067 (nat_lit 132871571) (nat_lit 10635306173) (nat_lit 0) A10K2.u8070 from rfl, allE_node, arows8067, irow8071, arows8070]
  all_goals rfl

theorem atot8071 : totK PA10K2 A10K2.u8071 = [0, 0, 868650652504, 6235756530896, 14641839312979, 13358184935963, 4322828777483, 389143828353, 6632180018, 0] := by
  rw [show A10K2.u8071 = KTree.node A10K2.u8067 (nat_lit 132871571) (nat_lit 10635306173) (nat_lit 0) A10K2.u8070 from rfl, totK_node, atot8067, atot8070]
  decide +kernel

theorem arows8079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8079 = true := by
  rw [show A10K2.u8079 = KTree.node A10K2.u8075 (nat_lit 132904222) (nat_lit 11488651514) (nat_lit 0) A10K2.u8078 from rfl, allE_node, arows8075, irow8079, arows8078]
  all_goals rfl

theorem atot8079 : totK PA10K2 A10K2.u8079 = [0, 0, 0, 1940485508492, 9718611427598, 16108158366085, 9785955133185, 1778136832142, 81733369668, 0] := by
  rw [show A10K2.u8079 = KTree.node A10K2.u8075 (nat_lit 132904222) (nat_lit 11488651514) (nat_lit 0) A10K2.u8078 from rfl, totK_node, atot8075, atot8078]
  decide +kernel

theorem arows8086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8086 = true := by
  rw [show A10K2.u8086 = KTree.node A10K2.u8082 (nat_lit 133002978) (nat_lit 13410586079) (nat_lit 0) A10K2.u8085 from rfl, allE_node, arows8082, irow8086, arows8085]
  all_goals rfl

theorem atot8086 : totK PA10K2 A10K2.u8086 = [0, 0, 0, 1385728585392, 7784314376430, 15103085571131, 11505647702667, 3203693402582, 295728240591, 7380853412] := by
  rw [show A10K2.u8086 = KTree.node A10K2.u8082 (nat_lit 133002978) (nat_lit 13410586079) (nat_lit 0) A10K2.u8085 from rfl, totK_node, atot8082, atot8085]
  decide +kernel

theorem arows8095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8095 = true := by
  rw [show A10K2.u8095 = KTree.node A10K2.u8091 (nat_lit 133104520) (nat_lit 14261625976) (nat_lit 0) A10K2.u8094 from rfl, allE_node, arows8091, irow8095, arows8094]
  all_goals rfl

theorem atot8095 : totK PA10K2 A10K2.u8095 = [0, 0, 0, 2699159623964, 11347370997661, 15718013686683, 8403256077801, 1419712732269, 63371181742, 0] := by
  rw [show A10K2.u8095 = KTree.node A10K2.u8091 (nat_lit 133104520) (nat_lit 14261625976) (nat_lit 0) A10K2.u8094 from rfl, totK_node, atot8091, atot8094]
  decide +kernel

theorem arows8102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8102 = true := by
  rw [show A10K2.u8102 = KTree.node A10K2.u8098 (nat_lit 133693881) (nat_lit 7182457248) (nat_lit 0) A10K2.u8101 from rfl, allE_node, arows8098, irow8102, arows8101]
  all_goals rfl

theorem atot8102 : totK PA10K2 A10K2.u8102 = [0, 0, 1361469227636, 6866018566229, 12830059078861, 11392312444674, 5568184705285, 1105731961784, 62382159641, 0] := by
  rw [show A10K2.u8102 = KTree.node A10K2.u8098 (nat_lit 133693881) (nat_lit 7182457248) (nat_lit 0) A10K2.u8101 from rfl, totK_node, atot8098, atot8101]
  decide +kernel

theorem arows8110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8110 = true := by
  rw [show A10K2.u8110 = KTree.node A10K2.u8106 (nat_lit 133728554) (nat_lit 4064473539) (nat_lit 128) A10K2.u8109 from rfl, allE_node, arows8106, irow8110, arows8109]
  all_goals rfl

theorem atot8110 : totK PA10K2 A10K2.u8110 = [0, 0, 719492328128, 5346273485695, 13728078163380, 14127597339893, 4975276707784, 489137567093, 12477124820, 0] := by
  rw [show A10K2.u8110 = KTree.node A10K2.u8106 (nat_lit 133728554) (nat_lit 4064473539) (nat_lit 128) A10K2.u8109 from rfl, totK_node, atot8106, atot8109]
  decide +kernel

theorem arows8117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8117 = true := by
  rw [show A10K2.u8117 = KTree.node A10K2.u8113 (nat_lit 133776853) (nat_lit 5287672699) (nat_lit 0) A10K2.u8116 from rfl, allE_node, arows8113, irow8117, arows8116]
  all_goals rfl

theorem atot8117 : totK PA10K2 A10K2.u8117 = [0, 0, 2088342423800, 9957965761952, 16033371216905, 9757211466756, 1985638976046, 90088615109, 0, 0] := by
  rw [show A10K2.u8117 = KTree.node A10K2.u8113 (nat_lit 133776853) (nat_lit 5287672699) (nat_lit 0) A10K2.u8116 from rfl, totK_node, atot8113, atot8116]
  decide +kernel

theorem arows8127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8127 = true := by
  rw [show A10K2.u8127 = KTree.node A10K2.u8123 (nat_lit 133813546) (nat_lit 12499765938) (nat_lit 0) A10K2.u8126 from rfl, allE_node, arows8123, irow8127, arows8126]
  all_goals rfl

theorem atot8127 : totK PA10K2 A10K2.u8127 = [0, 0, 762038499923, 5167759737175, 12988226989827, 14005929660649, 5510610606081, 568511111538, 12696458652, 0] := by
  rw [show A10K2.u8127 = KTree.node A10K2.u8123 (nat_lit 133813546) (nat_lit 12499765938) (nat_lit 0) A10K2.u8126 from rfl, totK_node, atot8123, atot8126]
  decide +kernel

theorem arows8134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8134 = true := by
  rw [show A10K2.u8134 = KTree.node A10K2.u8130 (nat_lit 133915576) (nat_lit 14037050343) (nat_lit 0) A10K2.u8133 from rfl, allE_node, arows8130, irow8134, arows8133]
  all_goals rfl

theorem atot8134 : totK PA10K2 A10K2.u8134 = [0, 0, 1662197905889, 8778205718321, 15877244659384, 10827225692536, 2249338054439, 98292843430, 0, 0] := by
  rw [show A10K2.u8134 = KTree.node A10K2.u8130 (nat_lit 133915576) (nat_lit 14037050343) (nat_lit 0) A10K2.u8133 from rfl, totK_node, atot8130, atot8133]
  decide +kernel

theorem arows8142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8142 = true := by
  rw [show A10K2.u8142 = KTree.node A10K2.u8138 (nat_lit 133938560) (nat_lit 14078414981) (nat_lit 0) A10K2.u8141 from rfl, allE_node, arows8138, irow8142, arows8141]
  all_goals rfl

theorem atot8142 : totK PA10K2 A10K2.u8142 = [0, 0, 0, 2169601182906, 10236180390176, 16036262635653, 9248173630933, 1617831300740, 75062079822, 0] := by
  rw [show A10K2.u8142 = KTree.node A10K2.u8138 (nat_lit 133938560) (nat_lit 14078414981) (nat_lit 0) A10K2.u8141 from rfl, totK_node, atot8138, atot8141]
  decide +kernel

theorem arows8149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8149 = true := by
  rw [show A10K2.u8149 = KTree.node A10K2.u8145 (nat_lit 133980936) (nat_lit 13953022228) (nat_lit 0) A10K2.u8148 from rfl, allE_node, arows8145, irow8149, arows8148]
  all_goals rfl

theorem atot8149 : totK PA10K2 A10K2.u8149 = [0, 0, 0, 1764863159099, 9279894902721, 16188153324469, 10160139463850, 1842592462656, 87325586775, 0] := by
  rw [show A10K2.u8149 = KTree.node A10K2.u8145 (nat_lit 133980936) (nat_lit 13953022228) (nat_lit 0) A10K2.u8148 from rfl, totK_node, atot8145, atot8148]
  decide +kernel

theorem arows8158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8158 = true := by
  rw [show A10K2.u8158 = KTree.node A10K2.u8154 (nat_lit 134031286) (nat_lit 16596548203) (nat_lit 0) A10K2.u8157 from rfl, allE_node, arows8154, irow8158, arows8157]
  all_goals rfl

theorem atot8158 : totK PA10K2 A10K2.u8158 = [0, 0, 0, 1760354472978, 8406676294332, 14551951943923, 11062789396133, 3187795021375, 312169436797, 6725424603] := by
  rw [show A10K2.u8158 = KTree.node A10K2.u8154 (nat_lit 134031286) (nat_lit 16596548203) (nat_lit 0) A10K2.u8157 from rfl, totK_node, atot8154, atot8157]
  decide +kernel

theorem arows8165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8165 = true := by
  rw [show A10K2.u8165 = KTree.node A10K2.u8161 (nat_lit 134066166) (nat_lit 16652602498) (nat_lit 0) A10K2.u8164 from rfl, allE_node, arows8161, irow8165, arows8164]
  all_goals rfl

theorem atot8165 : totK PA10K2 A10K2.u8165 = [0, 0, 0, 1032373587013, 6485258935973, 14314026255412, 13181444184036, 4176313730820, 385682273029, 6860445330] := by
  rw [show A10K2.u8165 = KTree.node A10K2.u8161 (nat_lit 134066166) (nat_lit 16652602498) (nat_lit 0) A10K2.u8164 from rfl, totK_node, atot8161, atot8164]
  decide +kernel

theorem arows8173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8173 = true := by
  rw [show A10K2.u8173 = KTree.node A10K2.u8169 (nat_lit 134167709) (nat_lit 5448880201) (nat_lit 0) A10K2.u8172 from rfl, allE_node, arows8169, irow8173, arows8172]
  all_goals rfl

theorem atot8173 : totK PA10K2 A10K2.u8173 = [0, 0, 0, 1696468033473, 9126588325648, 16088155963025, 10319966109568, 1886789623204, 86446547834, 0] := by
  rw [show A10K2.u8173 = KTree.node A10K2.u8169 (nat_lit 134167709) (nat_lit 5448880201) (nat_lit 0) A10K2.u8172 from rfl, totK_node, atot8169, atot8172]
  decide +kernel

theorem arows8180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8180 = true := by
  rw [show A10K2.u8180 = KTree.node A10K2.u8176 (nat_lit 134198966) (nat_lit 15439386157) (nat_lit 0) A10K2.u8179 from rfl, allE_node, arows8176, irow8180, arows8179]
  all_goals rfl

theorem atot8180 : totK PA10K2 A10K2.u8180 = [0, 0, 0, 0, 2177998751345, 10326686046028, 16028252897332, 8811656694263, 1553340253914, 73776485728] := by
  rw [show A10K2.u8180 = KTree.node A10K2.u8176 (nat_lit 134198966) (nat_lit 15439386157) (nat_lit 0) A10K2.u8179 from rfl, totK_node, atot8176, atot8179]
  decide +kernel

theorem arows14 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u14 = true := by
  rw [show A10K2.u14 = KTree.node A10K2.u6 (nat_lit 30143) (nat_lit 14245089115) (nat_lit 0) A10K2.u13 from rfl, allE_node, arows6, irow14, arows13]
  all_goals rfl

theorem atot14 : totK PA10K2 A10K2.u14 = [2495611015353, 13691282037523, 27720636794822, 24140735578199, 8204923190015, 986421564000, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u14 = KTree.node A10K2.u6 (nat_lit 30143) (nat_lit 14245089115) (nat_lit 0) A10K2.u13 from rfl, totK_node, atot6, atot13]
  decide +kernel

theorem arows29 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u29 = true := by
  rw [show A10K2.u29 = KTree.node A10K2.u21 (nat_lit 165943) (nat_lit 12016894450) (nat_lit 0) A10K2.u28 from rfl, allE_node, arows21, irow29, arows28]
  all_goals rfl

theorem atot29 : totK PA10K2 A10K2.u29 = [3177079300752, 16217568121509, 29210829010076, 21305736814782, 5583355916263, 487060562377, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u29 = KTree.node A10K2.u21 (nat_lit 165943) (nat_lit 12016894450) (nat_lit 0) A10K2.u28 from rfl, totK_node, atot21, atot28]
  decide +kernel

theorem arows45 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u45 = true := by
  rw [show A10K2.u45 = KTree.node A10K2.u37 (nat_lit 241564) (nat_lit 6334950940) (nat_lit 0) A10K2.u44 from rfl, allE_node, arows37, irow45, arows44]
  all_goals rfl

theorem atot45 : totK PA10K2 A10K2.u45 = [836280282984, 8171107409854, 24206445414571, 29256450669175, 14203686143295, 2367484576245, 105893753708, 0, 0, 0] := by
  rw [show A10K2.u45 = KTree.node A10K2.u37 (nat_lit 241564) (nat_lit 6334950940) (nat_lit 0) A10K2.u44 from rfl, totK_node, atot37, atot44]
  decide +kernel

theorem arows60 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u60 = true := by
  rw [show A10K2.u60 = KTree.node A10K2.u52 (nat_lit 311812) (nat_lit 11938764297) (nat_lit 0) A10K2.u59 from rfl, allE_node, arows52, irow60, arows59]
  all_goals rfl

theorem atot60 : totK PA10K2 A10K2.u60 = [0, 2475782306697, 14011977255367, 28176479924353, 23185401135281, 7351079159996, 924904139880, 36134558889, 0, 0] := by
  rw [show A10K2.u60 = KTree.node A10K2.u52 (nat_lit 311812) (nat_lit 11938764297) (nat_lit 0) A10K2.u59 from rfl, totK_node, atot52, atot59]
  decide +kernel

theorem arows77 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u77 = true := by
  rw [show A10K2.u77 = KTree.node A10K2.u69 (nat_lit 461154) (nat_lit 9800717754) (nat_lit 0) A10K2.u76 from rfl, allE_node, arows69, irow77, arows76]
  all_goals rfl

theorem atot77 : totK PA10K2 A10K2.u77 = [583967476257, 4720923206315, 16954533736581, 28878279155031, 20488201331500, 4968713970225, 368906305970, 5676195732, 0, 0] := by
  rw [show A10K2.u77 = KTree.node A10K2.u69 (nat_lit 461154) (nat_lit 9800717754) (nat_lit 0) A10K2.u76 from rfl, totK_node, atot69, atot76]
  decide +kernel

theorem arows92 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u92 = true := by
  rw [show A10K2.u92 = KTree.node A10K2.u84 (nat_lit 1083748) (nat_lit 13942558544) (nat_lit 0) A10K2.u91 from rfl, allE_node, arows84, irow92, arows91]
  all_goals rfl

theorem atot92 : totK PA10K2 A10K2.u92 = [2271998885316, 13108880794342, 27736597487360, 24623994819077, 8355384463539, 1005608587257, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u92 = KTree.node A10K2.u84 (nat_lit 1083748) (nat_lit 13942558544) (nat_lit 0) A10K2.u91 from rfl, totK_node, atot84, atot91]
  decide +kernel

theorem arows108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u108 = true := by
  rw [show A10K2.u108 = KTree.node A10K2.u100 (nat_lit 1182036) (nat_lit 13046691868) (nat_lit 0) A10K2.u107 from rfl, allE_node, arows100, irow108, arows107]
  all_goals rfl

theorem atot108 : totK PA10K2 A10K2.u108 = [2810590781981, 15205144215294, 28279363786280, 21468372938103, 6837280970874, 883085353961, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u108 = KTree.node A10K2.u100 (nat_lit 1182036) (nat_lit 13046691868) (nat_lit 0) A10K2.u107 from rfl, totK_node, atot100, atot107]
  decide +kernel

theorem arows123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u123 = true := by
  rw [show A10K2.u123 = KTree.node A10K2.u115 (nat_lit 1327684) (nat_lit 11135578240) (nat_lit 0) A10K2.u122 from rfl, allE_node, arows115, irow123, arows122]
  all_goals rfl

theorem atot123 : totK PA10K2 A10K2.u123 = [0, 5076422740980, 22371343512328, 31549502292274, 15018138777130, 2236336093928, 81833253981, 0, 0, 0] := by
  rw [show A10K2.u123 = KTree.node A10K2.u115 (nat_lit 1327684) (nat_lit 11135578240) (nat_lit 0) A10K2.u122 from rfl, totK_node, atot115, atot122]
  decide +kernel

theorem arows141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u141 = true := by
  rw [show A10K2.u141 = KTree.node A10K2.u133 (nat_lit 1462670) (nat_lit 11517503797) (nat_lit 0) A10K2.u140 from rfl, allE_node, arows133, irow141, arows140]
  all_goals rfl

theorem atot141 : totK PA10K2 A10K2.u141 = [844183794776, 5556736930706, 16874306488631, 27058356321352, 19141558810944, 4855950209144, 452395374723, 6354482628, 0, 0] := by
  rw [show A10K2.u141 = KTree.node A10K2.u133 (nat_lit 1462670) (nat_lit 11517503797) (nat_lit 0) A10K2.u140 from rfl, totK_node, atot133, atot140]
  decide +kernel

theorem arows156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u156 = true := by
  rw [show A10K2.u156 = KTree.node A10K2.u148 (nat_lit 1609768) (nat_lit 12834281164) (nat_lit 0) A10K2.u155 from rfl, allE_node, arows148, irow156, arows155]
  all_goals rfl

theorem atot156 : totK PA10K2 A10K2.u156 = [2636800723744, 14108597315980, 28197214376407, 24453457829947, 8309114933646, 1002780579962, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u156 = KTree.node A10K2.u148 (nat_lit 1609768) (nat_lit 12834281164) (nat_lit 0) A10K2.u155 from rfl, totK_node, atot148, atot155]
  decide +kernel

theorem arows172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u172 = true := by
  rw [show A10K2.u172 = KTree.node A10K2.u164 (nat_lit 1775714) (nat_lit 3778381636) (nat_lit 0) A10K2.u171 from rfl, allE_node, arows164, irow172, arows171]
  all_goals rfl

theorem atot172 : totK PA10K2 A10K2.u172 = [2404892320697, 14351641909377, 29868669346321, 25096763782460, 7652520619290, 761655922391, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u172 = KTree.node A10K2.u164 (nat_lit 1775714) (nat_lit 3778381636) (nat_lit 0) A10K2.u171 from rfl, totK_node, atot164, atot171]
  decide +kernel

theorem arows187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u187 = true := by
  rw [show A10K2.u187 = KTree.node A10K2.u179 (nat_lit 1838637) (nat_lit 5330896535) (nat_lit 0) A10K2.u186 from rfl, allE_node, arows179, irow187, arows186]
  all_goals rfl

theorem atot187 : totK PA10K2 A10K2.u187 = [0, 3712948709845, 18616730882984, 31703128664902, 20191547081775, 4060236224736, 205012054710, 0, 0, 0] := by
  rw [show A10K2.u187 = KTree.node A10K2.u179 (nat_lit 1838637) (nat_lit 5330896535) (nat_lit 0) A10K2.u186 from rfl, totK_node, atot179, atot186]
  decide +kernel

theorem arows204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u204 = true := by
  rw [show A10K2.u204 = KTree.node A10K2.u196 (nat_lit 1929618) (nat_lit 14171483272) (nat_lit 0) A10K2.u203 from rfl, allE_node, arows196, irow204, arows203]
  all_goals rfl

theorem atot204 : totK PA10K2 A10K2.u204 = [0, 2423621678898, 13666851168832, 28728661193192, 25847953442848, 8574685693195, 865231395041, 14159155365, 0, 0] := by
  rw [show A10K2.u204 = KTree.node A10K2.u196 (nat_lit 1929618) (nat_lit 14171483272) (nat_lit 0) A10K2.u203 from rfl, totK_node, atot196, atot203]
  decide +kernel

theorem arows219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u219 = true := by
  rw [show A10K2.u219 = KTree.node A10K2.u211 (nat_lit 2073770) (nat_lit 13057837668) (nat_lit 0) A10K2.u218 from rfl, allE_node, arows211, irow219, arows218]
  all_goals rfl

theorem atot219 : totK PA10K2 A10K2.u219 = [0, 2118442427748, 12286110012295, 26384723811187, 25659257430370, 10913469159617, 1657743196918, 73776485728, 0, 0] := by
  rw [show A10K2.u219 = KTree.node A10K2.u211 (nat_lit 2073770) (nat_lit 13057837668) (nat_lit 0) A10K2.u218 from rfl, totK_node, atot211, atot218]
  decide +kernel

theorem arows235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u235 = true := by
  rw [show A10K2.u235 = KTree.node A10K2.u227 (nat_lit 2133957) (nat_lit 2803837861) (nat_lit 0) A10K2.u234 from rfl, allE_node, arows227, irow235, arows234]
  all_goals rfl

theorem atot235 : totK PA10K2 A10K2.u235 = [0, 2303542125010, 13301785757337, 27899508563743, 24407695239466, 7971066223639, 957755710726, 36196801203, 0, 0] := by
  rw [show A10K2.u235 = KTree.node A10K2.u227 (nat_lit 2133957) (nat_lit 2803837861) (nat_lit 0) A10K2.u234 from rfl, totK_node, atot227, atot234]
  decide +kernel

theorem arows250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u250 = true := by
  rw [show A10K2.u250 = KTree.node A10K2.u242 (nat_lit 2279611) (nat_lit 5735086610) (nat_lit 0) A10K2.u249 from rfl, allE_node, arows242, irow250, arows249]
  all_goals rfl

theorem atot250 : totK PA10K2 A10K2.u250 = [0, 3325734164022, 17130426807499, 30364112521053, 20778314700551, 4704906409164, 330877777796, 5976421810, 0, 0] := by
  rw [show A10K2.u250 = KTree.node A10K2.u242 (nat_lit 2279611) (nat_lit 5735086610) (nat_lit 0) A10K2.u249 from rfl, totK_node, atot242, atot249]
  decide +kernel

theorem arows269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u269 = true := by
  rw [show A10K2.u269 = KTree.node A10K2.u261 (nat_lit 2359294) (nat_lit 15844512021) (nat_lit 0) A10K2.u268 from rfl, allE_node, arows261, irow269, arows268]
  all_goals rfl

theorem atot269 : totK PA10K2 A10K2.u269 = [0, 0, 5030740090305, 22500892014422, 32351494564764, 15708299829732, 2307152661542, 84865518449, 0, 0] := by
  rw [show A10K2.u269 = KTree.node A10K2.u261 (nat_lit 2359294) (nat_lit 15844512021) (nat_lit 0) A10K2.u268 from rfl, totK_node, atot261, atot268]
  decide +kernel

theorem arows284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u284 = true := by
  rw [show A10K2.u284 = KTree.node A10K2.u276 (nat_lit 2493210) (nat_lit 10932549264) (nat_lit 0) A10K2.u283 from rfl, allE_node, arows276, irow284, arows283]
  all_goals rfl

theorem atot284 : totK PA10K2 A10K2.u284 = [0, 0, 1991075320149, 12734317850101, 27802782887791, 23501723037217, 7549132290116, 948572371426, 36134558889, 0] := by
  rw [show A10K2.u284 = KTree.node A10K2.u276 (nat_lit 2493210) (nat_lit 10932549264) (nat_lit 0) A10K2.u283 from rfl, totK_node, atot276, atot283]
  decide +kernel

theorem arows300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u300 = true := by
  rw [show A10K2.u300 = KTree.node A10K2.u292 (nat_lit 2585033) (nat_lit 6828229770) (nat_lit 0) A10K2.u299 from rfl, allE_node, arows292, irow300, arows299]
  all_goals rfl

theorem atot300 : totK PA10K2 A10K2.u300 = [0, 2190250867092, 11816053071840, 23895991401035, 23595459247339, 12560682058793, 2992971491715, 283850832821, 5676195732, 0] := by
  rw [show A10K2.u300 = KTree.node A10K2.u292 (nat_lit 2585033) (nat_lit 6828229770) (nat_lit 0) A10K2.u299 from rfl, totK_node, atot292, atot299]
  decide +kernel

theorem arows315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u315 = true := by
  rw [show A10K2.u315 = KTree.node A10K2.u307 (nat_lit 3221179) (nat_lit 7122795149) (nat_lit 0) A10K2.u314 from rfl, allE_node, arows307, irow315, arows314]
  all_goals rfl

theorem atot315 : totK PA10K2 A10K2.u315 = [0, 1476036933430, 10373124242896, 26237602569730, 27133536233478, 9900533468813, 1211195743503, 42317974492, 0, 0] := by
  rw [show A10K2.u315 = KTree.node A10K2.u307 (nat_lit 3221179) (nat_lit 7122795149) (nat_lit 0) A10K2.u314 from rfl, totK_node, atot307, atot314]
  decide +kernel

theorem arows332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u332 = true := by
  rw [show A10K2.u332 = KTree.node A10K2.u324 (nat_lit 3309892) (nat_lit 12811252744) (nat_lit 0) A10K2.u331 from rfl, allE_node, arows324, irow332, arows331]
  all_goals rfl

theorem atot332 : totK PA10K2 A10K2.u332 = [0, 1996035672226, 12652301668233, 27516953572023, 24222589736857, 7950451122702, 1011727673085, 37172849495, 0, 0] := by
  rw [show A10K2.u332 = KTree.node A10K2.u324 (nat_lit 3309892) (nat_lit 12811252744) (nat_lit 0) A10K2.u331 from rfl, totK_node, atot324, atot331]
  decide +kernel

theorem arows347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u347 = true := by
  rw [show A10K2.u347 = KTree.node A10K2.u339 (nat_lit 3496201) (nat_lit 9227509640) (nat_lit 0) A10K2.u346 from rfl, allE_node, arows339, irow347, arows346]
  all_goals rfl

theorem atot347 : totK PA10K2 A10K2.u347 = [0, 0, 4809638147014, 22005184468575, 31919036892349, 14797466412837, 1967056809309, 62025894999, 0, 0] := by
  rw [show A10K2.u347 = KTree.node A10K2.u339 (nat_lit 3496201) (nat_lit 9227509640) (nat_lit 0) A10K2.u346 from rfl, totK_node, atot339, atot346]
  decide +kernel

theorem arows363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u363 = true := by
  rw [show A10K2.u363 = KTree.node A10K2.u355 (nat_lit 3687264) (nat_lit 12608668612) (nat_lit 0) A10K2.u362 from rfl, allE_node, arows355, irow363, arows362]
  all_goals rfl

theorem atot363 : totK PA10K2 A10K2.u363 = [0, 2209569436726, 11410333869453, 22902094400347, 23466168007401, 12943404763174, 3235866322167, 292013474143, 5976421810, 0] := by
  rw [show A10K2.u363 = KTree.node A10K2.u355 (nat_lit 3687264) (nat_lit 12608668612) (nat_lit 0) A10K2.u362 from rfl, totK_node, atot355, atot362]
  decide +kernel

theorem arows378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u378 = true := by
  rw [show A10K2.u378 = KTree.node A10K2.u370 (nat_lit 3778330) (nat_lit 14439833243) (nat_lit 0) A10K2.u377 from rfl, allE_node, arows370, irow378, arows377]
  all_goals rfl

theorem atot378 : totK PA10K2 A10K2.u378 = [0, 2797117292489, 15416493064950, 30284760117792, 24383691327553, 7105578017630, 605022746105, 7380853412, 0, 0] := by
  rw [show A10K2.u378 = KTree.node A10K2.u370 (nat_lit 3778330) (nat_lit 14439833243) (nat_lit 0) A10K2.u377 from rfl, totK_node, atot370, atot377]
  decide +kernel

theorem arows396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u396 = true := by
  rw [show A10K2.u396 = KTree.node A10K2.u388 (nat_lit 3913619) (nat_lit 10627624134) (nat_lit 0) A10K2.u395 from rfl, allE_node, arows388, irow396, arows395]
  all_goals rfl

theorem atot396 : totK PA10K2 A10K2.u396 = [1342080028200, 6528173001372, 14546266045583, 21931920977309, 22043698080230, 10558836074460, 1708779697389, 74781409772, 0, 0] := by
  rw [show A10K2.u396 = KTree.node A10K2.u388 (nat_lit 3913619) (nat_lit 10627624134) (nat_lit 0) A10K2.u395 from rfl, totK_node, atot388, atot395]
  decide +kernel

theorem arows411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u411 = true := by
  rw [show A10K2.u411 = KTree.node A10K2.u403 (nat_lit 8439003) (nat_lit 9755878341) (nat_lit 0) A10K2.u410 from rfl, allE_node, arows403, irow411, arows410]
  all_goals rfl

theorem atot411 : totK PA10K2 A10K2.u411 = [2255881713560, 13340575025070, 27991673211977, 24581947020567, 8316061558957, 999590668282, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u411 = KTree.node A10K2.u403 (nat_lit 8439003) (nat_lit 9755878341) (nat_lit 0) A10K2.u410 from rfl, totK_node, atot403, atot410]
  decide +kernel

theorem arows427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u427 = true := by
  rw [show A10K2.u427 = KTree.node A10K2.u419 (nat_lit 8575634) (nat_lit 14968544125) (nat_lit 0) A10K2.u426 from rfl, allE_node, arows419, irow427, arows426]
  all_goals rfl

theorem atot427 : totK PA10K2 A10K2.u427 = [2415627655432, 14156252659985, 29275450228082, 24378232250689, 6987445103019, 594566268330, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u427 = KTree.node A10K2.u419 (nat_lit 8575634) (nat_lit 14968544125) (nat_lit 0) A10K2.u426 from rfl, totK_node, atot419, atot426]
  decide +kernel

theorem arows442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u442 = true := by
  rw [show A10K2.u442 = KTree.node A10K2.u434 (nat_lit 8668947) (nat_lit 10409745941) (nat_lit 0) A10K2.u441 from rfl, allE_node, arows434, irow442, arows441]
  all_goals rfl

theorem atot442 : totK PA10K2 A10K2.u442 = [0, 3085243508555, 16282155922736, 29824297604557, 21739172348807, 6221120052758, 740952395126, 30605747850, 0, 0] := by
  rw [show A10K2.u442 = KTree.node A10K2.u434 (nat_lit 8668947) (nat_lit 10409745941) (nat_lit 0) A10K2.u441 from rfl, totK_node, atot434, atot441]
  decide +kernel

theorem arows459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u459 = true := by
  rw [show A10K2.u459 = KTree.node A10K2.u451 (nat_lit 8798819) (nat_lit 3764740548) (nat_lit 0) A10K2.u458 from rfl, allE_node, arows451, irow459, arows458]
  all_goals rfl

theorem atot459 : totK PA10K2 A10K2.u459 = [0, 2624054748386, 14565839070903, 28814178706634, 22776678208765, 6176002135578, 556871686912, 11205006771, 0, 0] := by
  rw [show A10K2.u459 = KTree.node A10K2.u451 (nat_lit 8798819) (nat_lit 3764740548) (nat_lit 0) A10K2.u458 from rfl, totK_node, atot451, atot458]
  decide +kernel

theorem arows474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u474 = true := by
  rw [show A10K2.u474 = KTree.node A10K2.u466 (nat_lit 8994019) (nat_lit 10290268136) (nat_lit 0) A10K2.u473 from rfl, allE_node, arows466, irow474, arows473]
  all_goals rfl

theorem atot474 : totK PA10K2 A10K2.u474 = [2185661584285, 12106805692415, 25509767253531, 25186197688828, 11607974230154, 2173546703501, 118764797727, 0, 0, 0] := by
  rw [show A10K2.u474 = KTree.node A10K2.u466 (nat_lit 8994019) (nat_lit 10290268136) (nat_lit 0) A10K2.u473 from rfl, totK_node, atot466, atot473]
  decide +kernel

theorem arows490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u490 = true := by
  rw [show A10K2.u490 = KTree.node A10K2.u482 (nat_lit 9057960) (nat_lit 5812190467) (nat_lit 0) A10K2.u489 from rfl, allE_node, arows482, irow490, arows489]
  all_goals rfl

theorem atot490 : totK PA10K2 A10K2.u490 = [2148948818715, 13448355981269, 28889881941101, 24585422395394, 7122105417470, 563468062107, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u490 = KTree.node A10K2.u482 (nat_lit 9057960) (nat_lit 5812190467) (nat_lit 0) A10K2.u489 from rfl, totK_node, atot482, atot489]
  decide +kernel

theorem arows505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u505 = true := by
  rw [show A10K2.u505 = KTree.node A10K2.u497 (nat_lit 9270509) (nat_lit 5416594490) (nat_lit 0) A10K2.u504 from rfl, allE_node, arows497, irow505, arows504]
  all_goals rfl

theorem atot505 : totK PA10K2 A10K2.u505 = [0, 2458745333827, 13919484619165, 28144455348801, 23517212807162, 7749073523656, 956449272788, 36704093874, 0, 0] := by
  rw [show A10K2.u505 = KTree.node A10K2.u497 (nat_lit 9270509) (nat_lit 5416594490) (nat_lit 0) A10K2.u504 from rfl, totK_node, atot497, atot504]
  decide +kernel

end QECKChecks.A10K2
