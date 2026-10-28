import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2820 = true := by
  decide +kernel

theorem tot2820 : totK PA10K2 A10K2.t2820 = [0, 603863138690, 2048195006246, 1954566059874, 446738255206, 13803479176, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2821 = true := by
  decide +kernel

theorem tot2821 : totK PA10K2 A10K2.t2821 = [0, 632678977999, 1946505435731, 1788261057822, 577426975901, 49107817395, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2822 = true := by
  decide +kernel

theorem tot2822 : totK PA10K2 A10K2.t2822 = [0, 425955474489, 1760585838464, 2014586651440, 562231719783, 32523532663, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2823 = true := by
  decide +kernel

theorem tot2823 : totK PA10K2 A10K2.t2823 = [0, 114748260487, 912436813076, 2028524114122, 1435820934170, 347370402244, 20331139758, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
