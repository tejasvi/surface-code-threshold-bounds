import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13004 = true := by
  decide +kernel

theorem tot13004 : totK PD2M8K2 D2M8K2.t13004 = [0, 0, 244576687239, 490650956635, 156352407589, 8470662040, 0, 0] := by
  decide +kernel

theorem rows13005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13005 = true := by
  decide +kernel

theorem tot13005 : totK PD2M8K2 D2M8K2.t13005 = [0, 174534810133, 394694784389, 248946632014, 75141561147, 3581949829, 0, 0] := by
  decide +kernel

theorem rows13006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13006 = true := by
  decide +kernel

theorem tot13006 : totK PD2M8K2 D2M8K2.t13006 = [0, 172137162750, 446580577763, 271647917670, 20944911235, 0, 0, 0] := by
  decide +kernel

theorem rows13007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13007 = true := by
  decide +kernel

theorem tot13007 : totK PD2M8K2 D2M8K2.t13007 = [0, 92722701599, 378038549168, 355690871963, 61776169652, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
