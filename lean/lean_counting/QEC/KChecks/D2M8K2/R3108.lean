import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12432 = true := by
  decide +kernel

theorem tot12432 : totK PD2M8K2 D2M8K2.t12432 = [0, 0, 244126602741, 499248917744, 146222365119, 3724448267, 0, 0] := by
  decide +kernel

theorem rows12433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12433 = true := by
  decide +kernel

theorem tot12433 : totK PD2M8K2 D2M8K2.t12433 = [0, 196857167206, 475259834240, 203913388993, 14234320945, 0, 0, 0] := by
  decide +kernel

theorem rows12434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12434 = true := by
  decide +kernel

theorem tot12434 : totK PD2M8K2 D2M8K2.t12434 = [0, 188208144465, 467030021255, 220053886131, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows12435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12435 = true := by
  decide +kernel

theorem tot12435 : totK PD2M8K2 D2M8K2.t12435 = [0, 20657074147, 296954562638, 451951198657, 88848179133, 1326647619, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
