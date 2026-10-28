import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows52 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t52 = true := by
  decide +kernel

theorem tot52 : totK PD2M8K2 D2M8K2.t52 = [0, 159742202801, 460572532871, 242327405187, 12200328444, 0, 0, 0] := by
  decide +kernel

theorem rows53 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t53 = true := by
  decide +kernel

theorem tot53 : totK PD2M8K2 D2M8K2.t53 = [0, 178876987196, 472109155340, 230454259271, 16917284594, 0, 0, 0] := by
  decide +kernel

theorem rows54 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t54 = true := by
  decide +kernel

theorem tot54 : totK PD2M8K2 D2M8K2.t54 = [0, 218475385317, 481115510910, 168534397908, 4978993093, 0, 0, 0] := by
  decide +kernel

theorem rows55 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t55 = true := by
  decide +kernel

theorem tot55 : totK PD2M8K2 D2M8K2.t55 = [0, 19330912284, 317372647130, 443537135945, 82565193424, 1206465782, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
