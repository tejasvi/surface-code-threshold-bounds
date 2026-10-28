import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4924 = true := by
  decide +kernel

theorem tot4924 : totK PD2M8K2 D2M8K2.t4924 = [0, 0, 152859201385, 347290639735, 306949801667, 114082270957, 6784511402, 0] := by
  decide +kernel

theorem rows4925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4925 = true := by
  decide +kernel

theorem tot4925 : totK PD2M8K2 D2M8K2.t4925 = [0, 0, 175722981939, 467187937899, 255680457944, 21493538004, 0, 0] := by
  decide +kernel

theorem rows4926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4926 = true := by
  decide +kernel

theorem tot4926 : totK PD2M8K2 D2M8K2.t4926 = [0, 0, 0, 306149325566, 507142938810, 107406207285, 1501162176, 0] := by
  decide +kernel

theorem rows4927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4927 = true := by
  decide +kernel

theorem tot4927 : totK PD2M8K2 D2M8K2.t4927 = [0, 0, 187681199742, 447784382774, 242527931727, 28712741237, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
