import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10416 = true := by
  decide +kernel

theorem tot10416 : totK PD2M8K2 D2M8K2.t10416 = [0, 0, 155426485780, 369961857759, 235878032270, 94545312080, 8913356732, 0] := by
  decide +kernel

theorem rows10417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10417 = true := by
  decide +kernel

theorem tot10417 : totK PD2M8K2 D2M8K2.t10417 = [0, 0, 187044405214, 465857259627, 225093476063, 13942354938, 0, 0] := by
  decide +kernel

theorem rows10418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10418 = true := by
  decide +kernel

theorem tot10418 : totK PD2M8K2 D2M8K2.t10418 = [0, 0, 67695407851, 332387074908, 389464235278, 82799135138, 1369150432, 0] := by
  decide +kernel

theorem rows10419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10419 = true := by
  decide +kernel

theorem tot10419 : totK PD2M8K2 D2M8K2.t10419 = [0, 0, 40039245341, 349094401251, 461956818988, 50856401441, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
