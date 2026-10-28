import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13920 = true := by
  decide +kernel

theorem tot13920 : totK PD2M8K2 D2M8K2.t13920 = [0, 174932382313, 447436309077, 256163233986, 25359931193, 0, 0, 0] := by
  decide +kernel

theorem rows13921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13921 = true := by
  decide +kernel

theorem tot13921 : totK PD2M8K2 D2M8K2.t13921 = [0, 216180025503, 495540156029, 190093065185, 5424570950, 0, 0, 0] := by
  decide +kernel

theorem rows13922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13922 = true := by
  decide +kernel

theorem tot13922 : totK PD2M8K2 D2M8K2.t13922 = [167132072890, 387938540318, 247667496979, 102128626423, 6804944647, 0, 0, 0] := by
  decide +kernel

theorem rows13923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13923 = true := by
  decide +kernel

theorem tot13923 : totK PD2M8K2 D2M8K2.t13923 = [158377051405, 446305605120, 265966254979, 18994842969, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
