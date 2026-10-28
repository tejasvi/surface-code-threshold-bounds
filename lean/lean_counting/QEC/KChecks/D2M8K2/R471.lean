import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1884 = true := by
  decide +kernel

theorem tot1884 : totK PD2M8K2 D2M8K2.t1884 = [0, 0, 271940229693, 507903028336, 111429296181, 1164319620, 0, 0] := by
  decide +kernel

theorem rows1885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1885 = true := by
  decide +kernel

theorem tot1885 : totK PD2M8K2 D2M8K2.t1885 = [0, 29121465226, 206170325098, 442287992984, 186497061869, 11885407614, 0, 0] := by
  decide +kernel

theorem rows1886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1886 = true := by
  decide +kernel

theorem tot1886 : totK PD2M8K2 D2M8K2.t1886 = [0, 206854628434, 507137034365, 189721393789, 2772644238, 0, 0, 0] := by
  decide +kernel

theorem rows1887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1887 = true := by
  decide +kernel

theorem tot1887 : totK PD2M8K2 D2M8K2.t1887 = [0, 87667209365, 372195244575, 350941951673, 63723751753, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
