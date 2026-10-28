import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1912 = true := by
  decide +kernel

theorem tot1912 : totK PD2M8K2 D2M8K2.t1912 = [0, 0, 258983788639, 439702550220, 190046872004, 19860731977, 0, 0] := by
  decide +kernel

theorem rows1913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1913 = true := by
  decide +kernel

theorem tot1913 : totK PD2M8K2 D2M8K2.t1913 = [0, 0, 179896579499, 488986023892, 226060813884, 6912449671, 0, 0] := by
  decide +kernel

theorem rows1914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1914 = true := by
  decide +kernel

theorem tot1914 : totK PD2M8K2 D2M8K2.t1914 = [0, 152754251528, 363314819404, 268786959717, 103116340548, 6804944647, 0, 0] := by
  decide +kernel

theorem rows1915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1915 = true := by
  decide +kernel

theorem tot1915 : totK PD2M8K2 D2M8K2.t1915 = [0, 163793364562, 440561772085, 275633051481, 29597579901, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
