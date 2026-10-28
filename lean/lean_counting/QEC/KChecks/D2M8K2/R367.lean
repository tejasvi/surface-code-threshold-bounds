import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1468 = true := by
  decide +kernel

theorem tot1468 : totK PD2M8K2 D2M8K2.t1468 = [0, 26852199204, 340070448821, 493040166406, 54278079389, 0, 0, 0] := by
  decide +kernel

theorem rows1469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1469 = true := by
  decide +kernel

theorem tot1469 : totK PD2M8K2 D2M8K2.t1469 = [0, 165645182481, 432924488025, 270856800647, 29675291715, 0, 0, 0] := by
  decide +kernel

theorem rows1470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1470 = true := by
  decide +kernel

theorem tot1470 : totK PD2M8K2 D2M8K2.t1470 = [0, 215255597221, 494072849506, 191097838167, 7856656896, 0, 0, 0] := by
  decide +kernel

theorem rows1471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1471 = true := by
  decide +kernel

theorem tot1471 : totK PD2M8K2 D2M8K2.t1471 = [0, 0, 244859066095, 450299515088, 191286428930, 18724171075, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
