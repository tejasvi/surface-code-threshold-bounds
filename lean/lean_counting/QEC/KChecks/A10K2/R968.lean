import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3872 = true := by
  decide +kernel

theorem tot3872 : totK PA10K2 A10K2.t3872 = [0, 493062864996, 1576045947424, 1486734445749, 398435226517, 25686058060, 229076674476, 429542201963, 142269073820, 6354482628] := by
  decide +kernel

theorem rows3873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3873 = true := by
  decide +kernel

theorem tot3873 : totK PA10K2 A10K2.t3873 = [0, 351656975343, 1624040599173, 2102505510202, 768111304454, 55925584929, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3874 = true := by
  decide +kernel

theorem tot3874 : totK PA10K2 A10K2.t3874 = [0, 0, 474387275089, 1761825517410, 1831755304016, 496249266170, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows3875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3875 = true := by
  decide +kernel

theorem tot3875 : totK PA10K2 A10K2.t3875 = [0, 394016424166, 1554713636150, 2052557307852, 865342498512, 84619529555, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
