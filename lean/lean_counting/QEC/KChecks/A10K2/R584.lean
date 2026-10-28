import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2336 = true := by
  decide +kernel

theorem tot2336 : totK PA10K2 A10K2.t2336 = [0, 0, 252075148608, 1536123643937, 2150904872923, 676383605054, 38585895272, 0, 0, 0] := by
  decide +kernel

theorem rows2337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2337 = true := by
  decide +kernel

theorem tot2337 : totK PA10K2 A10K2.t2337 = [0, 316846731414, 1057546355679, 1250134393275, 1131836379361, 775833295905, 153292242111, 5546304973, 0, 0] := by
  decide +kernel

theorem rows2338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2338 = true := by
  decide +kernel

theorem tot2338 : totK PA10K2 A10K2.t2338 = [0, 527310909255, 1924396823368, 1949628492615, 498626061658, 12244162943, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2339 = true := by
  decide +kernel

theorem tot2339 : totK PA10K2 A10K2.t2339 = [0, 0, 643852624580, 1995116910497, 1725221051626, 410428820309, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
