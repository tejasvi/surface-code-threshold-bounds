import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6736 = true := by
  decide +kernel

theorem tot6736 : totK PD2M8K2 D2M8K2.t6736 = [87238298500, 329279971611, 390730103444, 88651665847, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows6737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6737 = true := by
  decide +kernel

theorem tot6737 : totK PD2M8K2 D2M8K2.t6737 = [0, 202062047588, 455322842599, 188832229893, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows6738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6738 = true := by
  decide +kernel

theorem tot6738 : totK PD2M8K2 D2M8K2.t6738 = [170084889942, 457762503589, 253048131015, 26449984773, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6739 = true := by
  decide +kernel

theorem tot6739 : totK PD2M8K2 D2M8K2.t6739 = [153466458496, 450984725194, 259262402172, 19853346975, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
