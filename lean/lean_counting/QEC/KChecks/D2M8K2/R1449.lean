import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5796 = true := by
  decide +kernel

theorem tot5796 : totK PD2M8K2 D2M8K2.t5796 = [163433783747, 449889341695, 275888294209, 22748057846, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5797 = true := by
  decide +kernel

theorem tot5797 : totK PD2M8K2 D2M8K2.t5797 = [0, 228907912524, 492098608185, 160812133626, 4929677829, 0, 0, 0] := by
  decide +kernel

theorem rows5798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5798 = true := by
  decide +kernel

theorem tot5798 : totK PD2M8K2 D2M8K2.t5798 = [0, 177281717480, 458656895968, 225463254813, 14142725815, 0, 0, 0] := by
  decide +kernel

theorem rows5799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5799 = true := by
  decide +kernel

theorem tot5799 : totK PD2M8K2 D2M8K2.t5799 = [0, 182735830479, 451325663774, 271495227007, 27111785656, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
