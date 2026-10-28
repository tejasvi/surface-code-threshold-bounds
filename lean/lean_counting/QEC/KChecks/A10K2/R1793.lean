import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7172 = true := by
  decide +kernel

theorem tot7172 : totK PA10K2 A10K2.t7172 = [0, 295757175837, 1431603939018, 2228776661090, 1088687667228, 113120701584, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7173 = true := by
  decide +kernel

theorem tot7173 : totK PA10K2 A10K2.t7173 = [0, 0, 506085590180, 1777539854300, 2062208049700, 667173238176, 42633500131, 0, 0, 0] := by
  decide +kernel

theorem rows7174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7174 = true := by
  decide +kernel

theorem tot7174 : totK PA10K2 A10K2.t7174 = [0, 0, 476421592595, 1798333776548, 1932044583589, 506458697647, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows7175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7175 = true := by
  decide +kernel

theorem tot7175 : totK PA10K2 A10K2.t7175 = [0, 0, 147954321173, 1112863874240, 2067036063541, 1215312323025, 258751121198, 20060612110, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
