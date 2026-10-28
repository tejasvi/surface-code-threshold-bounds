import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3584 = true := by
  decide +kernel

theorem tot3584 : totK PA10K2 A10K2.t3584 = [0, 0, 302031194261, 1575530530894, 2117080714067, 664090076206, 38148714322, 0, 0, 0] := by
  decide +kernel

theorem rows3585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3585 = true := by
  decide +kernel

theorem tot3585 : totK PA10K2 A10K2.t3585 = [0, 0, 252731982766, 1068995256503, 1845600828507, 1181868107314, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3586 = true := by
  decide +kernel

theorem tot3586 : totK PA10K2 A10K2.t3586 = [0, 0, 436278166453, 1766000223248, 1994568987616, 549102212734, 31923522143, 0, 0, 0] := by
  decide +kernel

theorem rows3587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3587 = true := by
  decide +kernel

theorem tot3587 : totK PA10K2 A10K2.t3587 = [0, 0, 149173123673, 990624300882, 2001249302626, 1380171484490, 295447905770, 20070762815, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
