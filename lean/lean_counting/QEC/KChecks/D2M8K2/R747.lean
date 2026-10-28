import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2988 = true := by
  decide +kernel

theorem tot2988 : totK PD2M8K2 D2M8K2.t2988 = [0, 0, 195556793968, 466354152183, 195668901114, 12436572017, 0, 0] := by
  decide +kernel

theorem rows2989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2989 = true := by
  decide +kernel

theorem tot2989 : totK PD2M8K2 D2M8K2.t2989 = [0, 0, 160312167103, 473719740436, 218730855835, 11028107081, 0, 0] := by
  decide +kernel

theorem rows2990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2990 = true := by
  decide +kernel

theorem tot2990 : totK PD2M8K2 D2M8K2.t2990 = [0, 0, 217191448054, 488538814345, 158881520613, 4922956474, 0, 0] := by
  decide +kernel

theorem rows2991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2991 = true := by
  decide +kernel

theorem tot2991 : totK PD2M8K2 D2M8K2.t2991 = [0, 0, 209167228852, 491802382792, 186747117665, 5274443905, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
