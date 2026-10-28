import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4940 = true := by
  decide +kernel

theorem tot4940 : totK PA10K2 A10K2.t4940 = [0, 0, 369085573694, 1557770489008, 2055019910688, 797788520973, 60578866985, 0, 0, 0] := by
  decide +kernel

theorem rows4941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4941 = true := by
  decide +kernel

theorem tot4941 : totK PA10K2 A10K2.t4941 = [0, 0, 470522435901, 1811616530325, 1934824665626, 496868992344, 18827906493, 0, 0, 0] := by
  decide +kernel

theorem rows4942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4942 = true := by
  decide +kernel

theorem tot4942 : totK PA10K2 A10K2.t4942 = [0, 0, 0, 566972936464, 1922738851143, 1702619493986, 418518636383, 25565504801, 0, 0] := by
  decide +kernel

theorem rows4943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4943 = true := by
  decide +kernel

theorem tot4943 : totK PA10K2 A10K2.t4943 = [0, 0, 457723444173, 1639704797295, 1743652024225, 698162149194, 129188836268, 5453062850, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
