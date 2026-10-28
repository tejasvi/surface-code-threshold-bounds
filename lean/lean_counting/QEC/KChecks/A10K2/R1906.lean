import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7624 = true := by
  decide +kernel

theorem tot7624 : totK PA10K2 A10K2.t7624 = [0, 0, 17179869184, 896236645759, 2243003342708, 1575982780813, 269000922663, 6772895877, 0, 0] := by
  decide +kernel

theorem rows7625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7625 = true := by
  decide +kernel

theorem tot7625 : totK PA10K2 A10K2.t7625 = [0, 0, 0, 501483556200, 1927191249174, 2074549380506, 527504201931, 18736574845, 0, 0] := by
  decide +kernel

theorem rows7626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7626 = true := by
  decide +kernel

theorem tot7626 : totK PA10K2 A10K2.t7626 = [0, 0, 0, 561594759044, 1919897441365, 1926622129204, 566627943191, 49321567661, 0, 0] := by
  decide +kernel

theorem rows7627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7627 = true := by
  decide +kernel

theorem tot7627 : totK PA10K2 A10K2.t7627 = [0, 0, 0, 118860215929, 1015819421982, 2200871484158, 1404598176063, 217043516580, 6318667960, 0] := by
  decide +kernel

end QECKChecks.A10K2
