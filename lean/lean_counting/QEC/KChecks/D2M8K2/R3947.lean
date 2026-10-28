import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15788 = true := by
  decide +kernel

theorem tot15788 : totK PD2M8K2 D2M8K2.t15788 = [0, 182199800714, 456447934467, 254305812236, 27540025670, 0, 0, 0] := by
  decide +kernel

theorem rows15789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15789 = true := by
  decide +kernel

theorem tot15789 : totK PD2M8K2 D2M8K2.t15789 = [0, 189076141966, 462886002999, 224438812374, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows15790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15790 = true := by
  decide +kernel

theorem tot15790 : totK PD2M8K2 D2M8K2.t15790 = [0, 52184351020, 320026937719, 431570255763, 93851693363, 1198073392, 0, 0] := by
  decide +kernel

theorem rows15791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15791 = true := by
  decide +kernel

theorem tot15791 : totK PD2M8K2 D2M8K2.t15791 = [0, 0, 196312500243, 464861664852, 193896889658, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
