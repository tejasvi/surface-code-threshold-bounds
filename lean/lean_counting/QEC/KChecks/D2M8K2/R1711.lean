import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6844 = true := by
  decide +kernel

theorem tot6844 : totK PD2M8K2 D2M8K2.t6844 = [0, 199384360026, 474666395217, 195885151321, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows6845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6845 = true := by
  decide +kernel

theorem tot6845 : totK PD2M8K2 D2M8K2.t6845 = [172824233102, 460120429873, 254586432995, 25724187310, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6846 = true := by
  decide +kernel

theorem tot6846 : totK PD2M8K2 D2M8K2.t6846 = [198263592464, 462518917533, 236450313750, 18752362346, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6847 = true := by
  decide +kernel

theorem tot6847 : totK PD2M8K2 D2M8K2.t6847 = [56079040541, 322778398128, 415156569166, 96346271486, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
