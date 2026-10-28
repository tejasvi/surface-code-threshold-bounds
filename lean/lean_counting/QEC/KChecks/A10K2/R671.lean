import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2684 = true := by
  decide +kernel

theorem tot2684 : totK PA10K2 A10K2.t2684 = [0, 499730976493, 1859035200782, 2035719971446, 627222946632, 37938439775, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2685 = true := by
  decide +kernel

theorem tot2685 : totK PA10K2 A10K2.t2685 = [0, 0, 682222581627, 2101546812965, 1733126414055, 412755526817, 25715051306, 0, 0, 0] := by
  decide +kernel

theorem rows2686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2686 = true := by
  decide +kernel

theorem tot2686 : totK PA10K2 A10K2.t2686 = [0, 341612667258, 1321993376327, 2016146665621, 1228711065131, 206948457346, 5807182206, 0, 0, 0] := by
  decide +kernel

theorem rows2687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2687 = true := by
  decide +kernel

theorem tot2687 : totK PA10K2 A10K2.t2687 = [0, 456837649525, 1817916558365, 2091578307085, 682242873989, 39433076749, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
