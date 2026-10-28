import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9224 = true := by
  decide +kernel

theorem tot9224 : totK PD2M8K2 D2M8K2.t9224 = [155823973406, 443773195788, 256294644448, 19859907739, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9225 = true := by
  decide +kernel

theorem tot9225 : totK PD2M8K2 D2M8K2.t9225 = [59786597016, 313571613859, 410123785119, 97599874766, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows9226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9226 = true := by
  decide +kernel

theorem tot9226 : totK PD2M8K2 D2M8K2.t9226 = [74463668444, 366593325661, 410001589265, 51434991238, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9227 = true := by
  decide +kernel

theorem tot9227 : totK PD2M8K2 D2M8K2.t9227 = [165556443403, 438862487307, 281878000928, 30470231449, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
