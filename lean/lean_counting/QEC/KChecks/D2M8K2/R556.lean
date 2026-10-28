import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2224 = true := by
  decide +kernel

theorem tot2224 : totK PD2M8K2 D2M8K2.t2224 = [0, 0, 180423821000, 475577215073, 232720146534, 13916268439, 0, 0] := by
  decide +kernel

theorem rows2225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2225 = true := by
  decide +kernel

theorem tot2225 : totK PD2M8K2 D2M8K2.t2225 = [0, 0, 197113147271, 479921123126, 214382050694, 11477553491, 0, 0] := by
  decide +kernel

theorem rows2226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2226 = true := by
  decide +kernel

theorem tot2226 : totK PD2M8K2 D2M8K2.t2226 = [0, 0, 187781000600, 476351896664, 219293471605, 12439805748, 0, 0] := by
  decide +kernel

theorem rows2227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2227 = true := by
  decide +kernel

theorem tot2227 : totK PD2M8K2 D2M8K2.t2227 = [0, 0, 19233732584, 322375669537, 442036628839, 86867467791, 1171084559, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
