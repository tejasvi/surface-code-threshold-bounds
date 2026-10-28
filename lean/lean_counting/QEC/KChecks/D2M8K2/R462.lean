import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1848 = true := by
  decide +kernel

theorem tot1848 : totK PD2M8K2 D2M8K2.t1848 = [0, 0, 209591391940, 495864557552, 184624883632, 9587713104, 0, 0] := by
  decide +kernel

theorem rows1849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1849 = true := by
  decide +kernel

theorem tot1849 : totK PD2M8K2 D2M8K2.t1849 = [0, 84415941621, 308839629190, 391513292289, 100277750522, 3462014130, 0, 0] := by
  decide +kernel

theorem rows1850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1850 = true := by
  decide +kernel

theorem tot1850 : totK PD2M8K2 D2M8K2.t1850 = [0, 174894712533, 456890318988, 251504901483, 22307885334, 0, 0, 0] := by
  decide +kernel

theorem rows1851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1851 = true := by
  decide +kernel

theorem tot1851 : totK PD2M8K2 D2M8K2.t1851 = [0, 156825944409, 448697249265, 254118925456, 18093021161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
