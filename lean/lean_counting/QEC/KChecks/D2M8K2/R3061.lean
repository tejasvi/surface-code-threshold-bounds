import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12244 = true := by
  decide +kernel

theorem tot12244 : totK PD2M8K2 D2M8K2.t12244 = [162141363049, 451213682154, 282124639766, 30470231449, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12245 = true := by
  decide +kernel

theorem tot12245 : totK PD2M8K2 D2M8K2.t12245 = [204013064567, 481490901929, 214205602618, 11062980287, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12246 = true := by
  decide +kernel

theorem tot12246 : totK PD2M8K2 D2M8K2.t12246 = [31771015393, 268160497345, 401809643560, 186938238712, 21384324696, 0, 0, 0] := by
  decide +kernel

theorem rows12247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12247 = true := by
  decide +kernel

theorem tot12247 : totK PD2M8K2 D2M8K2.t12247 = [0, 199532031857, 487029546847, 205583486339, 7992090037, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
