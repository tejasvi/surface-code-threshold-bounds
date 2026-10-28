import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3380 = true := by
  decide +kernel

theorem tot3380 : totK PD2M8K2 D2M8K2.t3380 = [0, 0, 168801688868, 456273783734, 238055025657, 15055201367, 0, 0] := by
  decide +kernel

theorem rows3381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3381 = true := by
  decide +kernel

theorem tot3381 : totK PD2M8K2 D2M8K2.t3381 = [0, 0, 197965901912, 470283008252, 191465907353, 10834652844, 0, 0] := by
  decide +kernel

theorem rows3382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3382 = true := by
  decide +kernel

theorem tot3382 : totK PD2M8K2 D2M8K2.t3382 = [0, 0, 194199272985, 464307215974, 200053921986, 11929814841, 0, 0] := by
  decide +kernel

theorem rows3383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3383 = true := by
  decide +kernel

theorem tot3383 : totK PD2M8K2 D2M8K2.t3383 = [0, 0, 19228354030, 341910293102, 402553983586, 64585035854, 1095107716, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
