import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7656 = true := by
  decide +kernel

theorem tot7656 : totK PD2M8K2 D2M8K2.t7656 = [0, 0, 86420403140, 354925435949, 371105095024, 71320193788, 1164319620, 0] := by
  decide +kernel

theorem rows7657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7657 = true := by
  decide +kernel

theorem tot7657 : totK PD2M8K2 D2M8K2.t7657 = [0, 0, 0, 246341013540, 487515945520, 150798362652, 8423393484, 0] := by
  decide +kernel

theorem rows7658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7658 = true := by
  decide +kernel

theorem tot7658 : totK PD2M8K2 D2M8K2.t7658 = [0, 0, 140474466605, 374009633786, 289494870219, 73807812135, 3462014130, 0] := by
  decide +kernel

theorem rows7659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7659 = true := by
  decide +kernel

theorem tot7659 : totK PD2M8K2 D2M8K2.t7659 = [0, 0, 179781905953, 486257496144, 202052272721, 6276281593, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
