import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2816 = true := by
  decide +kernel

theorem tot2816 : totK PD2M8K2 D2M8K2.t2816 = [0, 184821976878, 479624814699, 221505403141, 10372117509, 0, 0, 0] := by
  decide +kernel

theorem rows2817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2817 = true := by
  decide +kernel

theorem tot2817 : totK PD2M8K2 D2M8K2.t2817 = [0, 193243749756, 447589218163, 218229432609, 16861767938, 0, 0, 0] := by
  decide +kernel

theorem rows2818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2818 = true := by
  decide +kernel

theorem tot2818 : totK PD2M8K2 D2M8K2.t2818 = [0, 174566715383, 500430172505, 217036636351, 5265834820, 0, 0, 0] := by
  decide +kernel

theorem rows2819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2819 = true := by
  decide +kernel

theorem tot2819 : totK PD2M8K2 D2M8K2.t2819 = [0, 177656653819, 462084790703, 244143176256, 14878906560, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
