import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t900 = true := by
  decide +kernel

theorem tot900 : totK PD2M8K2 D2M8K2.t900 = [33000947677, 201499513660, 441625774735, 188303755939, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t901 = true := by
  decide +kernel

theorem tot901 : totK PD2M8K2 D2M8K2.t901 = [195090286429, 467959900357, 225068135165, 18516688092, 0, 0, 0, 0] := by
  decide +kernel

theorem rows902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t902 = true := by
  decide +kernel

theorem tot902 : totK PD2M8K2 D2M8K2.t902 = [183849917033, 471628788090, 228748089718, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t903 = true := by
  decide +kernel

theorem tot903 : totK PD2M8K2 D2M8K2.t903 = [0, 282885458859, 496279432233, 110496441239, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
