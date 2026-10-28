import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16380 = true := by
  decide +kernel

theorem tot16380 : totK PD2M8K2 D2M8K2.t16380 = [0, 0, 0, 177422665713, 457166757121, 247745872116, 21322691856, 0] := by
  decide +kernel

theorem rows16381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16381 = true := by
  decide +kernel

theorem tot16381 : totK PD2M8K2 D2M8K2.t16381 = [0, 0, 0, 156144296609, 450656560949, 280803990882, 21276629933, 0] := by
  decide +kernel

theorem rows16382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16382 = true := by
  decide +kernel

theorem tot16382 : totK PD2M8K2 D2M8K2.t16382 = [0, 0, 0, 0, 234383507854, 473339734599, 146713432685, 4811815119] := by
  decide +kernel

theorem rows16383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16383 = true := by
  decide +kernel

theorem tot16383 : totK PD2M8K2 D2M8K2.t16383 = [0, 0, 0, 0, 176439480030, 452298977959, 218907312639, 16939352947] := by
  decide +kernel

end QECKChecks.D2M8K2
