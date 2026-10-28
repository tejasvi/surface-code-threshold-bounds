import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10928 = true := by
  decide +kernel

theorem tot10928 : totK PD2M8K2 D2M8K2.t10928 = [0, 0, 168796203834, 485928075570, 251377036775, 11888899831, 0, 0] := by
  decide +kernel

theorem rows10929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10929 = true := by
  decide +kernel

theorem tot10929 : totK PD2M8K2 D2M8K2.t10929 = [0, 0, 169925313841, 450204184412, 250765318430, 24400623909, 0, 0] := by
  decide +kernel

theorem rows10930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10930 = true := by
  decide +kernel

theorem tot10930 : totK PD2M8K2 D2M8K2.t10930 = [0, 0, 199639504819, 465280327592, 209795306248, 12116787427, 0, 0] := by
  decide +kernel

theorem rows10931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10931 = true := by
  decide +kernel

theorem tot10931 : totK PD2M8K2 D2M8K2.t10931 = [0, 0, 31273251518, 334651154735, 446089965243, 73241240251, 1075657031, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
