import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4020 = true := by
  decide +kernel

theorem tot4020 : totK PD2M8K2 D2M8K2.t4020 = [0, 157463152400, 373258275799, 274392492537, 108379522061, 6804944647, 0, 0] := by
  decide +kernel

theorem rows4021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4021 = true := by
  decide +kernel

theorem tot4021 : totK PD2M8K2 D2M8K2.t4021 = [0, 177805552528, 446366988671, 262375352321, 25176653962, 0, 0, 0] := by
  decide +kernel

theorem rows4022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4022 = true := by
  decide +kernel

theorem tot4022 : totK PD2M8K2 D2M8K2.t4022 = [0, 87489962043, 369613594044, 362662676462, 64939816682, 0, 0, 0] := by
  decide +kernel

theorem rows4023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4023 = true := by
  decide +kernel

theorem tot4023 : totK PD2M8K2 D2M8K2.t4023 = [0, 0, 262457046102, 488224295414, 150619992323, 8154189357, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
