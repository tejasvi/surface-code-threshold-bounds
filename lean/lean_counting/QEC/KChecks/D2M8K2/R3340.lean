import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13360 = true := by
  decide +kernel

theorem tot13360 : totK PD2M8K2 D2M8K2.t13360 = [0, 158403939145, 479788114587, 263190383585, 14946791381, 0, 0, 0] := by
  decide +kernel

theorem rows13361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13361 = true := by
  decide +kernel

theorem tot13361 : totK PD2M8K2 D2M8K2.t13361 = [0, 0, 201426455239, 463334391144, 222859492267, 20932498298, 0, 0] := by
  decide +kernel

theorem rows13362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13362 = true := by
  decide +kernel

theorem tot13362 : totK PD2M8K2 D2M8K2.t13362 = [0, 0, 179978921182, 481285061003, 227812556238, 9404016956, 0, 0] := by
  decide +kernel

theorem rows13363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13363 = true := by
  decide +kernel

theorem tot13363 : totK PD2M8K2 D2M8K2.t13363 = [0, 148367227349, 366338066842, 274474561782, 104285017890, 4607200788, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
