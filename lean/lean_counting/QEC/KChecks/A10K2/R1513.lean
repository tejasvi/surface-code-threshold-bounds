import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6052 = true := by
  decide +kernel

theorem tot6052 : totK PA10K2 A10K2.t6052 = [0, 630819432655, 2039814127292, 1707336027246, 398608464455, 25295400199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6053 = true := by
  decide +kernel

theorem tot6053 : totK PA10K2 A10K2.t6053 = [284288764057, 1309322300388, 2012942624121, 1152998692877, 192847946769, 5453753178, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6054 = true := by
  decide +kernel

theorem tot6054 : totK PA10K2 A10K2.t6054 = [401593501827, 1687185454322, 2146750016696, 847128783788, 72265510083, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6055 = true := by
  decide +kernel

theorem tot6055 : totK PA10K2 A10K2.t6055 = [109233960067, 774281091858, 1964114630770, 1741245775687, 409567817063, 24865484814, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
