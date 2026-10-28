import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4760 = true := by
  decide +kernel

theorem tot4760 : totK PA10K2 A10K2.t4760 = [0, 0, 966798389723, 2358783999850, 1255876094006, 113491970078, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4761 = true := by
  decide +kernel

theorem tot4761 : totK PA10K2 A10K2.t4761 = [0, 0, 448056785648, 1857242647216, 1899578175479, 481224196234, 31558137809, 0, 0, 0] := by
  decide +kernel

theorem rows4762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4762 = true := by
  decide +kernel

theorem tot4762 : totK PA10K2 A10K2.t4762 = [0, 0, 500821982819, 1895960198765, 1918375264787, 475904677171, 26944146327, 0, 0, 0] := by
  decide +kernel

theorem rows4763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4763 = true := by
  decide +kernel

theorem tot4763 : totK PA10K2 A10K2.t4763 = [0, 0, 463954090620, 1792942570836, 2018336980047, 537588915350, 18754734689, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
