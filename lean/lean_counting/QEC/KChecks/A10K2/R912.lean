import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3648 = true := by
  decide +kernel

theorem tot3648 : totK PA10K2 A10K2.t3648 = [0, 0, 277975932046, 1142009495543, 1859763070835, 1216130345223, 208812330670, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3649 = true := by
  decide +kernel

theorem tot3649 : totK PA10K2 A10K2.t3649 = [0, 0, 464297345805, 1832369677719, 1926706476609, 500023395610, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows3650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3650 = true := by
  decide +kernel

theorem tot3650 : totK PA10K2 A10K2.t3650 = [0, 0, 0, 765472652696, 2308238540722, 1405541188598, 122772188958, 0, 0, 0] := by
  decide +kernel

theorem rows3651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3651 = true := by
  decide +kernel

theorem tot3651 : totK PA10K2 A10K2.t3651 = [0, 0, 576535847275, 1906849653575, 1853201963054, 653438292105, 124049193463, 6239673734, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
