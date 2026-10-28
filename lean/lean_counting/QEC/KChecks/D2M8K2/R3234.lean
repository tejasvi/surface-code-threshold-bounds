import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12936 = true := by
  decide +kernel

theorem tot12936 : totK PD2M8K2 D2M8K2.t12936 = [0, 0, 156859154155, 460735661463, 246696268149, 16954741265, 0, 0] := by
  decide +kernel

theorem rows12937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12937 = true := by
  decide +kernel

theorem tot12937 : totK PD2M8K2 D2M8K2.t12937 = [0, 0, 178453182671, 451095233384, 272807636054, 27111785656, 0, 0] := by
  decide +kernel

theorem rows12938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12938 = true := by
  decide +kernel

theorem tot12938 : totK PD2M8K2 D2M8K2.t12938 = [0, 0, 196268700416, 483188930049, 218255346989, 10315032832, 0, 0] := by
  decide +kernel

theorem rows12939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12939 = true := by
  decide +kernel

theorem tot12939 : totK PD2M8K2 D2M8K2.t12939 = [0, 0, 59165842109, 317578195185, 394491125169, 134463194967, 9929822194, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
