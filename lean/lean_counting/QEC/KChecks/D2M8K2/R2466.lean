import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9864 = true := by
  decide +kernel

theorem tot9864 : totK PD2M8K2 D2M8K2.t9864 = [0, 150540897751, 383948168633, 294704663526, 73871422983, 1409560813, 0, 0] := by
  decide +kernel

theorem rows9865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9865 = true := by
  decide +kernel

theorem tot9865 : totK PD2M8K2 D2M8K2.t9865 = [0, 189512382418, 465620997661, 218056342832, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows9866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9866 = true := by
  decide +kernel

theorem tot9866 : totK PD2M8K2 D2M8K2.t9866 = [0, 36256159624, 306905394813, 451450718222, 89812559935, 1164319620, 0, 0] := by
  decide +kernel

theorem rows9867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9867 = true := by
  decide +kernel

theorem tot9867 : totK PD2M8K2 D2M8K2.t9867 = [0, 18440543662, 201529908775, 455342365574, 177288329298, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
