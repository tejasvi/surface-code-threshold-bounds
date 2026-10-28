import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3812 = true := by
  decide +kernel

theorem tot3812 : totK PD2M8K2 D2M8K2.t3812 = [0, 179771020165, 458203900682, 227710400918, 18446688069, 0, 0, 0] := by
  decide +kernel

theorem rows3813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3813 = true := by
  decide +kernel

theorem tot3813 : totK PD2M8K2 D2M8K2.t3813 = [0, 179573282924, 475826857545, 220679589744, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows3814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3814 = true := by
  decide +kernel

theorem tot3814 : totK PD2M8K2 D2M8K2.t3814 = [0, 107276325239, 417799514277, 317983384041, 29181541580, 0, 0, 0] := by
  decide +kernel

theorem rows3815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3815 = true := by
  decide +kernel

theorem tot3815 : totK PD2M8K2 D2M8K2.t3815 = [0, 22044255984, 316746907140, 461746263176, 79547673924, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
