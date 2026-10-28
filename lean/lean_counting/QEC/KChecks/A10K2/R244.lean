import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t976 = true := by
  decide +kernel

theorem tot976 : totK PA10K2 A10K2.t976 = [0, 0, 575294727692, 1946925912897, 1885174896710, 461113126054, 11598176779, 0, 0, 0] := by
  decide +kernel

theorem rows977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t977 = true := by
  decide +kernel

theorem tot977 : totK PA10K2 A10K2.t977 = [0, 0, 0, 741629948993, 2219470854311, 1666656984453, 256265438967, 6066958478, 0, 0] := by
  decide +kernel

theorem rows978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t978 = true := by
  decide +kernel

theorem tot978 : totK PA10K2 A10K2.t978 = [0, 0, 0, 435914999770, 1758566650468, 2048360600196, 646813124810, 29031327120, 0, 0] := by
  decide +kernel

theorem rows979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t979 = true := by
  decide +kernel

theorem tot979 : totK PA10K2 A10K2.t979 = [0, 0, 567282221012, 1915667969418, 1784035207516, 447780152372, 89811417463, 26011840508, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
