import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14376 = true := by
  decide +kernel

theorem tot14376 : totK PD2M8K2 D2M8K2.t14376 = [0, 0, 103269177444, 344567671250, 303082484220, 76664202519, 3552795014, 0] := by
  decide +kernel

theorem rows14377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14377 = true := by
  decide +kernel

theorem tot14377 : totK PD2M8K2 D2M8K2.t14377 = [0, 0, 191808974431, 467937071004, 221931400523, 14517393958, 0, 0] := by
  decide +kernel

theorem rows14378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14378 = true := by
  decide +kernel

theorem tot14378 : totK PD2M8K2 D2M8K2.t14378 = [0, 88972639724, 333850276673, 344674179274, 125856177018, 8935385149, 0, 0] := by
  decide +kernel

theorem rows14379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14379 = true := by
  decide +kernel

theorem tot14379 : totK PD2M8K2 D2M8K2.t14379 = [0, 184786212975, 450692529273, 225263821220, 17049520876, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
