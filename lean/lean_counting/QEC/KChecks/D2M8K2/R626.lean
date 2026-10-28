import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2504 = true := by
  decide +kernel

theorem tot2504 : totK PD2M8K2 D2M8K2.t2504 = [0, 182638964787, 472398954156, 254519833784, 20821767404, 0, 0, 0] := by
  decide +kernel

theorem rows2505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2505 = true := by
  decide +kernel

theorem tot2505 : totK PD2M8K2 D2M8K2.t2505 = [0, 174790829062, 470466001550, 236545495111, 12752126925, 0, 0, 0] := by
  decide +kernel

theorem rows2506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2506 = true := by
  decide +kernel

theorem tot2506 : totK PD2M8K2 D2M8K2.t2506 = [0, 0, 256207567917, 482983819137, 128500148665, 2305904642, 0, 0] := by
  decide +kernel

theorem rows2507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2507 = true := by
  decide +kernel

theorem tot2507 : totK PD2M8K2 D2M8K2.t2507 = [0, 64702258243, 258948388061, 371085157595, 142627288536, 10710292732, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
