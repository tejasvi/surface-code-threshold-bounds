import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1008 = true := by
  decide +kernel

theorem tot1008 : totK PD2M8K2 D2M8K2.t1008 = [104347464638, 346773261995, 346022960056, 95943768101, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows1009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1009 = true := by
  decide +kernel

theorem tot1009 : totK PD2M8K2 D2M8K2.t1009 = [182627655224, 456409965100, 255033313575, 27541771463, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1010 = true := by
  decide +kernel

theorem tot1010 : totK PD2M8K2 D2M8K2.t1010 = [34646529138, 313156124579, 446005909248, 104031847302, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows1011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1011 = true := by
  decide +kernel

theorem tot1011 : totK PD2M8K2 D2M8K2.t1011 = [0, 190922784300, 466406462889, 217707268114, 17063213105, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
