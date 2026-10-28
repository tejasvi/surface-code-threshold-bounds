import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12792 = true := by
  decide +kernel

theorem tot12792 : totK PD2M8K2 D2M8K2.t12792 = [0, 93574619190, 383777902628, 396799233865, 55292823989, 0, 0, 0] := by
  decide +kernel

theorem rows12793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12793 = true := by
  decide +kernel

theorem tot12793 : totK PD2M8K2 D2M8K2.t12793 = [0, 162259835704, 444135472852, 285344731505, 24207123315, 0, 0, 0] := by
  decide +kernel

theorem rows12794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12794 = true := by
  decide +kernel

theorem tot12794 : totK PD2M8K2 D2M8K2.t12794 = [0, 173125932643, 464894994531, 242725761085, 12049505048, 0, 0, 0] := by
  decide +kernel

theorem rows12795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12795 = true := by
  decide +kernel

theorem tot12795 : totK PD2M8K2 D2M8K2.t12795 = [0, 0, 173747851437, 445705303225, 262590280595, 25364689049, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
