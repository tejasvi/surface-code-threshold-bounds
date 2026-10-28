import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15548 = true := by
  decide +kernel

theorem tot15548 : totK PD2M8K2 D2M8K2.t15548 = [0, 85137499363, 398491747932, 373330237897, 44078637025, 0, 0, 0] := by
  decide +kernel

theorem rows15549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15549 = true := by
  decide +kernel

theorem tot15549 : totK PD2M8K2 D2M8K2.t15549 = [0, 68480167219, 310244252273, 421078475992, 107018033120, 3880716147, 0, 0] := by
  decide +kernel

theorem rows15550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15550 = true := by
  decide +kernel

theorem tot15550 : totK PD2M8K2 D2M8K2.t15550 = [0, 177731433298, 456313991656, 265617971165, 24491063341, 0, 0, 0] := by
  decide +kernel

theorem rows15551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15551 = true := by
  decide +kernel

theorem tot15551 : totK PD2M8K2 D2M8K2.t15551 = [0, 173035511169, 475140128579, 251285036345, 16437329297, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
