import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4576 = true := by
  decide +kernel

theorem tot4576 : totK PD2M8K2 D2M8K2.t4576 = [0, 0, 87893730914, 361244266940, 361856729125, 93281612123, 9460398152, 0] := by
  decide +kernel

theorem rows4577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4577 = true := by
  decide +kernel

theorem tot4577 : totK PD2M8K2 D2M8K2.t4577 = [0, 0, 0, 225434718724, 473528152969, 196766208689, 9106631530, 0] := by
  decide +kernel

theorem rows4578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4578 = true := by
  decide +kernel

theorem tot4578 : totK PD2M8K2 D2M8K2.t4578 = [0, 0, 85528477217, 260385630488, 386544930017, 155234048530, 5521894595, 0] := by
  decide +kernel

theorem rows4579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4579 = true := by
  decide +kernel

theorem tot4579 : totK PD2M8K2 D2M8K2.t4579 = [0, 0, 183111027323, 470903115589, 254371238339, 22387985911, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
