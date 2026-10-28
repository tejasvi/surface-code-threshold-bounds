import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10684 = true := by
  decide +kernel

theorem tot10684 : totK PD2M8K2 D2M8K2.t10684 = [0, 0, 0, 239717230602, 501933872248, 126995681632, 2519764721, 0] := by
  decide +kernel

theorem rows10685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10685 = true := by
  decide +kernel

theorem tot10685 : totK PD2M8K2 D2M8K2.t10685 = [0, 0, 0, 222326476337, 501159068930, 145572404576, 2447226230, 0] := by
  decide +kernel

theorem rows10686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10686 = true := by
  decide +kernel

theorem tot10686 : totK PD2M8K2 D2M8K2.t10686 = [0, 0, 0, 237085030884, 477399650834, 158759622758, 9544739469, 0] := by
  decide +kernel

theorem rows10687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10687 = true := by
  decide +kernel

theorem tot10687 : totK PD2M8K2 D2M8K2.t10687 = [0, 0, 0, 232040969607, 481308072986, 151801932556, 4078100393, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
