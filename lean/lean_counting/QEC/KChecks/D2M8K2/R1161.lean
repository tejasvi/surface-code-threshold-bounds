import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4644 = true := by
  decide +kernel

theorem tot4644 : totK PD2M8K2 D2M8K2.t4644 = [0, 0, 199736259266, 428485186923, 275088431637, 37525057781, 0, 0] := by
  decide +kernel

theorem rows4645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4645 = true := by
  decide +kernel

theorem tot4645 : totK PD2M8K2 D2M8K2.t4645 = [0, 0, 125790953353, 474189373139, 300893908222, 22100121687, 0, 0] := by
  decide +kernel

theorem rows4646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4646 = true := by
  decide +kernel

theorem tot4646 : totK PD2M8K2 D2M8K2.t4646 = [0, 0, 36666380604, 288411407676, 472885401754, 116958966923, 1510868091, 0] := by
  decide +kernel

theorem rows4647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4647 = true := by
  decide +kernel

theorem tot4647 : totK PD2M8K2 D2M8K2.t4647 = [0, 0, 191658551246, 461013148820, 244324086560, 22695155496, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
