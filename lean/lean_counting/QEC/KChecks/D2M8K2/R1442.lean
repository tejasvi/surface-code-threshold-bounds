import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5768 = true := by
  decide +kernel

theorem tot5768 : totK PD2M8K2 D2M8K2.t5768 = [0, 0, 230383758138, 505042971777, 151300950812, 5138457373, 0, 0] := by
  decide +kernel

theorem rows5769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5769 = true := by
  decide +kernel

theorem tot5769 : totK PD2M8K2 D2M8K2.t5769 = [0, 103392314000, 396430850916, 354866684296, 48264497063, 0, 0, 0] := by
  decide +kernel

theorem rows5770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5770 = true := by
  decide +kernel

theorem tot5770 : totK PD2M8K2 D2M8K2.t5770 = [0, 189313045087, 446250718520, 248186816291, 27131002818, 0, 0, 0] := by
  decide +kernel

theorem rows5771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5771 = true := by
  decide +kernel

theorem tot5771 : totK PD2M8K2 D2M8K2.t5771 = [0, 88850125907, 375942254786, 361667768734, 58601925218, 1162515529, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
