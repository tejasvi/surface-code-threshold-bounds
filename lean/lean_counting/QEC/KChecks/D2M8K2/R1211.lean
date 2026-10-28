import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4844 = true := by
  decide +kernel

theorem tot4844 : totK PD2M8K2 D2M8K2.t4844 = [0, 0, 173154768708, 466623958660, 247174880161, 12128450978, 0, 0] := by
  decide +kernel

theorem rows4845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4845 = true := by
  decide +kernel

theorem tot4845 : totK PD2M8K2 D2M8K2.t4845 = [0, 0, 0, 250494278187, 517517970857, 136886339876, 0, 0] := by
  decide +kernel

theorem rows4846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4846 = true := by
  decide +kernel

theorem tot4846 : totK PD2M8K2 D2M8K2.t4846 = [0, 0, 63807048300, 256446320303, 391562798676, 146728286351, 9190730223, 0] := by
  decide +kernel

theorem rows4847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4847 = true := by
  decide +kernel

theorem tot4847 : totK PD2M8K2 D2M8K2.t4847 = [0, 0, 169110641951, 483968093318, 248074828185, 22962869647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
