import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9292 = true := by
  decide +kernel

theorem tot9292 : totK PD2M8K2 D2M8K2.t9292 = [168471524745, 413996033964, 301035092149, 37820638953, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9293 = true := by
  decide +kernel

theorem tot9293 : totK PD2M8K2 D2M8K2.t9293 = [186066182565, 456924698988, 235732168437, 16971693599, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9294 = true := by
  decide +kernel

theorem tot9294 : totK PD2M8K2 D2M8K2.t9294 = [68188677921, 366606147345, 369616528152, 96144679181, 12086244250, 0, 0, 0] := by
  decide +kernel

theorem rows9295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9295 = true := by
  decide +kernel

theorem tot9295 : totK PD2M8K2 D2M8K2.t9295 = [0, 171810180533, 456243549881, 245305591514, 15097029224, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
