import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t628 = true := by
  decide +kernel

theorem tot628 : totK PD2M8K2 D2M8K2.t628 = [155221297835, 435045299002, 284268571195, 41889818630, 0, 0, 0, 0] := by
  decide +kernel

theorem rows629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t629 = true := by
  decide +kernel

theorem tot629 : totK PD2M8K2 D2M8K2.t629 = [175316794091, 439741554018, 258866688588, 22739538314, 0, 0, 0, 0] := by
  decide +kernel

theorem rows630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t630 = true := by
  decide +kernel

theorem tot630 : totK PD2M8K2 D2M8K2.t630 = [65867739944, 354912001672, 396066462925, 76491109362, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t631 = true := by
  decide +kernel

theorem tot631 : totK PD2M8K2 D2M8K2.t631 = [23827933371, 271484653823, 471279798014, 124842160936, 3880716147, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
