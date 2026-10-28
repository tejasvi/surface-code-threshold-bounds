import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4544 = true := by
  decide +kernel

theorem tot4544 : totK PD2M8K2 D2M8K2.t4544 = [0, 0, 0, 306507772737, 495078369831, 89106732172, 1164319620, 0] := by
  decide +kernel

theorem rows4545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4545 = true := by
  decide +kernel

theorem tot4545 : totK PD2M8K2 D2M8K2.t4545 = [0, 0, 131635274643, 434085389960, 304958514371, 22731349118, 0, 0] := by
  decide +kernel

theorem rows4546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4546 = true := by
  decide +kernel

theorem tot4546 : totK PD2M8K2 D2M8K2.t4546 = [0, 0, 175017595963, 458080317388, 236131249239, 15073263762, 0, 0] := by
  decide +kernel

theorem rows4547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4547 = true := by
  decide +kernel

theorem tot4547 : totK PD2M8K2 D2M8K2.t4547 = [0, 0, 89959375667, 362728337914, 357575505512, 59750636938, 1096505104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
