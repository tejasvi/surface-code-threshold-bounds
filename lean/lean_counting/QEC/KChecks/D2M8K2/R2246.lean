import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8984 = true := by
  decide +kernel

theorem tot8984 : totK PD2M8K2 D2M8K2.t8984 = [0, 188342988512, 493957632436, 212207654421, 7810344689, 0, 0, 0] := by
  decide +kernel

theorem rows8985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8985 = true := by
  decide +kernel

theorem tot8985 : totK PD2M8K2 D2M8K2.t8985 = [88158716638, 299102647832, 342548706872, 153282263359, 8213711289, 0, 0, 0] := by
  decide +kernel

theorem rows8986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8986 = true := by
  decide +kernel

theorem tot8986 : totK PD2M8K2 D2M8K2.t8986 = [181938142650, 452301646749, 261154463140, 27595624084, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8987 = true := by
  decide +kernel

theorem tot8987 : totK PD2M8K2 D2M8K2.t8987 = [52776158027, 321711241881, 431923611799, 88614031927, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
