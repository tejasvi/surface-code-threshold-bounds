import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8140 = true := by
  decide +kernel

theorem tot8140 : totK PD2M8K2 D2M8K2.t8140 = [0, 0, 157595174203, 447131780014, 281228796001, 21224989134, 0, 0] := by
  decide +kernel

theorem rows8141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8141 = true := by
  decide +kernel

theorem tot8141 : totK PD2M8K2 D2M8K2.t8141 = [0, 0, 201412039980, 473102648696, 223028535954, 14309813652, 0, 0] := by
  decide +kernel

theorem rows8142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8142 = true := by
  decide +kernel

theorem tot8142 : totK PD2M8K2 D2M8K2.t8142 = [0, 0, 189996479982, 472533949846, 232510251618, 16104584588, 0, 0] := by
  decide +kernel

theorem rows8143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8143 = true := by
  decide +kernel

theorem tot8143 : totK PD2M8K2 D2M8K2.t8143 = [0, 0, 193165850377, 475039224284, 216244109270, 12183533023, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
