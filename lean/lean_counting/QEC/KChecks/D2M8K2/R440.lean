import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1760 = true := by
  decide +kernel

theorem tot1760 : totK PD2M8K2 D2M8K2.t1760 = [0, 0, 171977936135, 451256984724, 233294624260, 16954357240, 0, 0] := by
  decide +kernel

theorem rows1761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1761 = true := by
  decide +kernel

theorem tot1761 : totK PD2M8K2 D2M8K2.t1761 = [0, 0, 119962333563, 419220604731, 319300439463, 31206320367, 0, 0] := by
  decide +kernel

theorem rows1762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1762 = true := by
  decide +kernel

theorem tot1762 : totK PD2M8K2 D2M8K2.t1762 = [0, 0, 0, 272096321263, 498540281254, 106942244326, 1369150432, 0] := by
  decide +kernel

theorem rows1763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1763 = true := by
  decide +kernel

theorem tot1763 : totK PD2M8K2 D2M8K2.t1763 = [0, 0, 156141088578, 440743096770, 292655433465, 27846060793, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
