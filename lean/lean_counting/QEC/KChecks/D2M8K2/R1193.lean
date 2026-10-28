import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4772 = true := by
  decide +kernel

theorem tot4772 : totK PD2M8K2 D2M8K2.t4772 = [0, 0, 311005182887, 525447285521, 86774116462, 0, 0, 0] := by
  decide +kernel

theorem rows4773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4773 = true := by
  decide +kernel

theorem tot4773 : totK PD2M8K2 D2M8K2.t4773 = [0, 0, 188407221938, 489423028898, 188181446505, 6406394852, 0, 0] := by
  decide +kernel

theorem rows4774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4774 = true := by
  decide +kernel

theorem tot4774 : totK PD2M8K2 D2M8K2.t4774 = [0, 0, 171954313511, 469884200181, 220402064678, 12063983151, 0, 0] := by
  decide +kernel

theorem rows4775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4775 = true := by
  decide +kernel

theorem tot4775 : totK PD2M8K2 D2M8K2.t4775 = [0, 0, 52782444535, 330528765751, 392753132851, 67608634458, 1138244013, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
