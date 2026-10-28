import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2472 = true := by
  decide +kernel

theorem tot2472 : totK PA10K2 A10K2.t2472 = [0, 115487560146, 638204095028, 1770271271789, 1998402921745, 581565167519, 43911449185, 0, 0, 0] := by
  decide +kernel

theorem rows2473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2473 = true := by
  decide +kernel

theorem tot2473 : totK PA10K2 A10K2.t2473 = [0, 464012183237, 1858945466053, 1940905587231, 467707093735, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2474 = true := by
  decide +kernel

theorem tot2474 : totK PA10K2 A10K2.t2474 = [0, 187388126195, 983908074927, 1922663754866, 1405462257969, 334459139324, 20070762815, 0, 0, 0] := by
  decide +kernel

theorem rows2475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2475 = true := by
  decide +kernel

theorem tot2475 : totK PA10K2 A10K2.t2475 = [0, 248290791297, 1047358802245, 1891735568270, 1348519801335, 225068933673, 10760911071, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
